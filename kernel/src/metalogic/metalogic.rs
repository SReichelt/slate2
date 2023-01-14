use std::{fmt::Debug, rc::Rc};

use smallvec::SmallVec;

use super::expr::*;

use crate::generic::{context::*, context_object::*, expr::*};

pub struct MetaLogic {
    constants: Vec<Param>,
    reduction_rules: Vec<ReductionRule>,
    lambda_handler: Box<dyn LambdaHandler>,
}

pub type ParamInit<'a> = (&'a str, &'a str);
pub type ReductionRuleInit<'a> = (&'a [ParamInit<'a>], &'a str, &'a str);

impl MetaLogic {
    pub fn construct<F>(
        constants_init: &[ParamInit],
        reduction_rules_init: &[ReductionRuleInit],
        create_lambda_handler: F,
    ) -> Result<Self, String>
    where
        F: FnOnce(&Context<Param>) -> Box<dyn LambdaHandler>,
    {
        let mut constants: Vec<Param> = constants_init
            .iter()
            .map(|(name, _)| Param {
                name: Some(Rc::new((*name).into())),
                type_expr: Expr::default(),
            })
            .collect();

        let lambda_handler = create_lambda_handler(&Context::new(&constants));

        let mut idx = 0;
        for (_, type_str) in constants_init {
            let ctx = Context::new(&constants);
            constants[idx].type_expr = Expr::parse(type_str, &ctx, lambda_handler.as_ref())?;
            idx += 1;
        }

        let root_ctx = Context::new(&constants);

        let reduction_rules: Result<Vec<ReductionRule>, String> = reduction_rules_init
            .iter()
            .map(|(params_init, source_init, target_init)| {
                let mut params = SmallVec::with_capacity(params_init.len());
                for (name, type_str) in params_init.iter() {
                    let ctx = root_ctx.with_locals(&params);
                    params.push(Param {
                        name: Some(Rc::new((*name).into())),
                        type_expr: Expr::parse(type_str, &ctx, lambda_handler.as_ref())?,
                    })
                }
                let ctx = root_ctx.with_locals(&params);
                let source = Expr::parse(source_init, &ctx, lambda_handler.as_ref())?;
                let target = Expr::parse(target_init, &ctx, lambda_handler.as_ref())?;
                Ok(ReductionRule {
                    params,
                    body: ReductionBody { source, target },
                })
            })
            .collect();

        Ok(MetaLogic {
            constants,
            reduction_rules: reduction_rules?,
            lambda_handler,
        })
    }

    pub fn get_root_context(&self) -> Context<Param> {
        Context::new(&self.constants)
    }

    pub fn get_constant(&self, name: &str) -> Option<&Param> {
        let ctx = self.get_root_context();
        let var_idx = ctx.get_var_index(name, 0)?;
        Some(ctx.get_var(var_idx))
    }

    pub fn get_reduction_rules(&self) -> &[ReductionRule] {
        &self.reduction_rules
    }

    pub fn parse_expr(&self, s: &str, ctx: &Context<Param>) -> Result<Expr, String> {
        Expr::parse(s, ctx, self.lambda_handler.as_ref())
    }

    pub fn print_expr(&self, expr: &Expr, ctx: &Context<Param>) -> String {
        expr.print(ctx, self.lambda_handler.as_ref())
    }

    pub fn reduce_expr(
        &self,
        expr: &mut Expr,
        ctx: &Context<Param>,
        convert_to_combinators: bool,
    ) -> bool {
        expr.reduce(self, ctx.locals_start(), convert_to_combinators)
    }

    pub fn get_expr_type(&self, expr: &Expr, ctx: &Context<Param>) -> Result<Expr, String> {
        match expr {
            Expr::Var(Var(idx)) => Ok(ctx.shifted_to_context(&ctx.get_var(*idx).type_expr, *idx)),
            Expr::App(app) => {
                // Finding the result type of an application is surprisingly tricky because the
                // application itself does not include the type parameters of its function. Instead,
                // to determine the property we need to match the type of the actual function
                // argument against a term that denotes a sufficiently generic pi type. Then we
                // apply the property to the argument of the application.
                let fun = &app.param;
                let arg = &app.body;
                let fun_type = self.get_expr_type(fun, ctx)?;
                let arg_type = self.get_expr_type(arg, ctx)?;
                let locals_start = ctx.locals_start();
                let (prop_param, cmp_fun_type) = self.lambda_handler.get_semi_generic_dep_type(
                    arg_type,
                    DependentTypeCtorKind::Pi,
                    locals_start,
                )?;
                if let Some(mut prop_vec) =
                    fun_type.match_expr(&Some(self), &[prop_param], &cmp_fun_type, locals_start)
                {
                    let prop = prop_vec.pop().unwrap();
                    Ok(Expr::apply(prop, arg.clone(), locals_start))
                } else {
                    let fun_str = self.print_expr(fun, ctx);
                    let fun_type_str = self.print_expr(&fun_type, ctx);
                    let arg_str = self.print_expr(arg, ctx);
                    let arg_type = self.get_expr_type(arg, ctx)?;
                    let arg_type_str = self.print_expr(&arg_type, ctx);
                    Err(format!("application type mismatch: {fun_str} : {fun_type_str} cannot be applied to {arg_str} : {arg_type_str}"))
                }
            }
            Expr::Lambda(lambda) => {
                let body_ctx = ctx.with_local(&lambda.param);
                let body_type = self.get_expr_type(&lambda.body, &body_ctx)?;
                let body_type_lambda = Expr::lambda(lambda.param.clone(), body_type);
                self.lambda_handler.get_dep_type(
                    lambda.param.type_expr.clone(),
                    body_type_lambda,
                    DependentTypeCtorKind::Pi,
                    ctx.locals_start(),
                )
            }
        }
    }

    pub fn check_reduction_rule_types(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        let root_ctx = self.get_root_context();

        for rule in &self.reduction_rules {
            if let Err(error) = self.check_reduction_rule_type(rule, &root_ctx) {
                errors.push(error);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn check_reduction_rule_type(
        &self,
        rule: &ReductionRule,
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        let rule_ctx = ctx.with_locals(&rule.params);
        let source_type = self.get_expr_type(&rule.body.source, &rule_ctx)?;
        let target_type = self.get_expr_type(&rule.body.target, &rule_ctx)?;
        if source_type.compare(rule_ctx.locals_start(), &target_type, &Some(self)) {
            Ok(())
        } else {
            let source_str = self.print_expr(&rule.body.source, &rule_ctx);
            let source_type_str = self.print_expr(&source_type, &rule_ctx);
            let target_str = self.print_expr(&rule.body.target, &rule_ctx);
            let target_type_str = self.print_expr(&target_type, &rule_ctx);
            Err(format!("type conflict in reduction rule between {source_str} : {source_type_str} and {target_str} : {target_type_str}"))
        }
    }

    pub fn check_type_of_types(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        let root_ctx = self.get_root_context();

        for constant in &self.constants {
            if let Err(error) = self.check_type_of_types_in_param(constant, &root_ctx) {
                errors.push(error);
            }
        }

        for rule in &self.reduction_rules {
            if let Err(error) = self.check_type_of_types_in_reduction_rule(rule, &root_ctx) {
                errors.push(error);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn check_type_of_types_in_param(
        &self,
        param: &Param,
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        self.check_type_of_types_in_expr(&param.type_expr, ctx)?;
        let type_type = self.get_expr_type(&param.type_expr, ctx)?;
        let cmp_type_type = self.lambda_handler.get_universe_type()?;
        if type_type.compare(ctx.locals_start(), &cmp_type_type, &Some(self)) {
            Ok(())
        } else {
            let type_str = self.print_expr(&param.type_expr, &ctx);
            let type_type_str = self.print_expr(&type_type, &ctx);
            let cmp_type_type_str = self.print_expr(&cmp_type_type, &ctx);
            Err(format!("parameter type {type_str} : {type_type_str} must have type {cmp_type_type_str} instead"))
        }
    }

    fn check_type_of_types_in_params(
        &self,
        params: &[Param],
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        for param_idx in 0..params.len() {
            let param = &params[param_idx];
            let param_ctx = ctx.with_locals(&params[0..param_idx]);
            self.check_type_of_types_in_param(param, &param_ctx)?;
        }
        Ok(())
    }

    fn check_type_of_types_in_expr(&self, expr: &Expr, ctx: &Context<Param>) -> Result<(), String> {
        match expr {
            Expr::Var(_) => {}
            Expr::App(app) => {
                self.check_type_of_types_in_expr(&app.param, ctx)?;
                self.check_type_of_types_in_expr(&app.body, ctx)?;
            }
            Expr::Lambda(lambda) => {
                self.check_type_of_types_in_param(&lambda.param, ctx)?;
                let body_ctx = ctx.with_local(&lambda.param);
                self.check_type_of_types_in_expr(&lambda.body, &body_ctx)?;
            }
        };
        Ok(())
    }

    fn check_type_of_types_in_reduction_rule(
        &self,
        rule: &ReductionRule,
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        self.check_type_of_types_in_params(&rule.params, ctx)?;
        let rule_ctx = ctx.with_locals(&rule.params);
        self.check_type_of_types_in_expr(&rule.body.source, &rule_ctx)?;
        self.check_type_of_types_in_expr(&rule.body.target, &rule_ctx)?;
        Ok(())
    }
}

pub type ReductionRule = MultiLambda<Param, ReductionBody>;

pub struct ReductionBody {
    pub source: Expr,
    pub target: Expr,
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum DependentTypeCtorKind {
    Pi,
    Sigma,
}

pub trait LambdaHandler {
    fn get_universe_type(&self) -> Result<Expr, String>;

    fn get_dep_type(
        &self,
        domain: Expr,
        prop: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<Expr, String>;

    fn get_indep_type(
        &self,
        domain: Expr,
        codomain: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<Expr, String> {
        let prop = Expr::const_lambda(domain.clone(), codomain, locals_start);
        self.get_dep_type(domain, prop, kind, locals_start)
    }

    fn get_prop_type(&self, domain: Expr, locals_start: VarIndex) -> Result<Expr, String> {
        self.get_indep_type(
            domain,
            self.get_universe_type()?,
            DependentTypeCtorKind::Pi,
            locals_start,
        )
    }

    fn get_semi_generic_dep_type(
        &self,
        domain: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<(Param, Expr), String> {
        let domain_in_prop_var_ctx = domain.with_shifted_vars(locals_start, 0, -1);
        let prop_param = Param {
            name: None,
            type_expr: self.get_prop_type(domain, locals_start)?,
        };
        let prop_var = Expr::var(-1);
        let dep_type =
            self.get_dep_type(domain_in_prop_var_ctx, prop_var, kind, locals_start - 1)?;
        Ok((prop_param, dep_type))
    }

    fn get_generic_dep_type(
        &self,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<(Param, Param, Expr), String> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let domain_var = Expr::var(-1);
        let (prop_param, dep_type) =
            self.get_semi_generic_dep_type(domain_var, kind, locals_start - 1)?;
        Ok((domain_param, prop_param, dep_type))
    }

    fn get_generic_indep_type(
        &self,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<(Param, Param, Expr), String> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let codomain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let domain_var = Expr::var(-2);
        let codomain_var = Expr::var(-1);
        let indep_type = self.get_indep_type(domain_var, codomain_var, kind, locals_start - 2)?;
        Ok((domain_param, codomain_param, indep_type))
    }

    fn get_id_cmb(&self, domain: Expr, locals_start: VarIndex) -> Result<Expr, String>;

    fn get_const_cmb(
        &self,
        domain: Expr,
        codomain: Expr,
        locals_start: VarIndex,
    ) -> Result<Expr, String>;

    fn get_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        prop2: Expr,
        locals_start: VarIndex,
    ) -> Result<Expr, String>;
}

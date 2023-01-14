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
            let ctx = MetaLogicContext {
                context: Context::new(&constants),
                reduction_rules: &[],
                lambda_handler: lambda_handler.as_ref(),
            };
            constants[idx].type_expr = Expr::parse(type_str, &ctx)?;
            idx += 1;
        }

        let root_ctx = MetaLogicContext {
            context: Context::new(&constants),
            reduction_rules: &[],
            lambda_handler: lambda_handler.as_ref(),
        };

        let reduction_rules: Result<Vec<ReductionRule>, String> = reduction_rules_init
            .iter()
            .map(|(params_init, source_init, target_init)| {
                let mut params = SmallVec::with_capacity(params_init.len());
                for (name, type_str) in params_init.iter() {
                    let ctx = root_ctx.with_locals(&params);
                    params.push(Param {
                        name: Some(Rc::new((*name).into())),
                        type_expr: Expr::parse(type_str, &ctx)?,
                    })
                }
                let ctx = root_ctx.with_locals(&params);
                let source = Expr::parse(source_init, &ctx)?;
                let target = Expr::parse(target_init, &ctx)?;
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

    pub fn get_root_context(&self) -> MetaLogicContext {
        MetaLogicContext {
            context: Context::new(&self.constants),
            reduction_rules: &self.reduction_rules,
            lambda_handler: self.lambda_handler.as_ref(),
        }
    }

    pub fn get_constant(&self, name: &str) -> Option<&Param> {
        let ctx = self.get_root_context();
        let var_idx = ctx.context.get_var_index(name, 0)?;
        Some(ctx.context.get_var(var_idx))
    }

    pub fn parse_expr(&self, s: &str) -> Result<Expr, String> {
        Expr::parse(s, &self.get_root_context())
    }

    pub fn print_expr(&self, expr: &Expr) -> String {
        expr.print(&self.get_root_context())
    }

    pub fn reduce_expr(&self, expr: &mut Expr, convert_to_combinators: bool) -> bool {
        expr.reduce(&self.get_root_context(), convert_to_combinators)
    }

    pub fn get_expr_type(&self, expr: &Expr) -> Result<Expr, String> {
        expr.get_type(&self.get_root_context())
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
        ctx: &MetaLogicContext,
    ) -> Result<(), String> {
        let rule_ctx = ctx.with_locals(&rule.params);
        let source_type = rule.body.source.get_type(&rule_ctx)?;
        let target_type = rule.body.target.get_type(&rule_ctx)?;
        if source_type.compare(
            rule_ctx.context.locals_start(),
            &target_type,
            &Some(&self.reduction_rules),
        ) {
            Ok(())
        } else {
            let source_str = rule.body.source.print(&rule_ctx);
            let source_type_str = source_type.print(&rule_ctx);
            let target_str = rule.body.target.print(&rule_ctx);
            let target_type_str = target_type.print(&rule_ctx);
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
        ctx: &MetaLogicContext,
    ) -> Result<(), String> {
        self.check_type_of_types_in_expr(&param.type_expr, ctx)?;
        let type_type = param.type_expr.get_type(ctx)?;
        let cmp_type_type = self.lambda_handler.get_universe_type()?;
        if type_type.compare(
            ctx.context.locals_start(),
            &cmp_type_type,
            &Some(&self.reduction_rules),
        ) {
            Ok(())
        } else {
            let type_str = param.type_expr.print(&ctx);
            let type_type_str = type_type.print(&ctx);
            let cmp_type_type_str = cmp_type_type.print(&ctx);
            Err(format!("parameter type {type_str} : {type_type_str} must have type {cmp_type_type_str} instead"))
        }
    }

    fn check_type_of_types_in_params(
        &self,
        params: &[Param],
        ctx: &MetaLogicContext,
    ) -> Result<(), String> {
        for param_idx in 0..params.len() {
            let param = &params[param_idx];
            let param_ctx = ctx.with_locals(&params[0..param_idx]);
            self.check_type_of_types_in_param(param, &param_ctx)?;
        }
        Ok(())
    }

    fn check_type_of_types_in_expr(
        &self,
        expr: &Expr,
        ctx: &MetaLogicContext,
    ) -> Result<(), String> {
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
        ctx: &MetaLogicContext,
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

pub struct MetaLogicContext<'a, 'b: 'a, 'c> {
    pub context: Context<'a, 'b, 'c, Param>,
    pub reduction_rules: &'a [ReductionRule],
    pub lambda_handler: &'a dyn LambdaHandler,
}

impl<'a, 'b, 'c> MetaLogicContext<'a, 'b, 'c> {
    pub fn with_local<'d, 'e>(&'e self, param: &'d Param) -> MetaLogicContext<'d, 'b, 'e>
    where
        'a: 'd,
        'c: 'e,
    {
        MetaLogicContext {
            context: self.context.with_local(param),
            reduction_rules: self.reduction_rules,
            lambda_handler: self.lambda_handler,
        }
    }

    pub fn with_locals<'d, 'e>(&'e self, params: &'d [Param]) -> MetaLogicContext<'d, 'b, 'e>
    where
        'a: 'd,
        'c: 'e,
    {
        MetaLogicContext {
            context: self.context.with_locals(params),
            reduction_rules: self.reduction_rules,
            lambda_handler: self.lambda_handler,
        }
    }
}

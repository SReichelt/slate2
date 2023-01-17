use std::{fmt::Debug, rc::Rc};

use smallvec::SmallVec;

use super::expr::*;

use crate::generic::{context::*, context_object::*, expr::*};

pub struct MetaLogic {
    pub constants: Vec<Param>,
    pub reduction_rules: Vec<ReductionRule>,
    pub lambda_handler: Box<dyn LambdaHandler>,
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
        F: FnOnce(&[Param]) -> Box<dyn LambdaHandler>,
    {
        let constants: Vec<Param> = constants_init
            .iter()
            .map(|(name, _)| Param {
                name: Some(Rc::new((*name).into())),
                type_expr: Expr::default(),
            })
            .collect();

        let lambda_handler = create_lambda_handler(&constants);

        let mut metalogic = MetaLogic {
            constants,
            reduction_rules: Vec::with_capacity(reduction_rules_init.len()),
            lambda_handler,
        };

        let mut idx = 0;
        for (_, type_str) in constants_init {
            let type_expr = Expr::parse(type_str, &metalogic.get_root_context())?;
            metalogic.constants[idx].type_expr = type_expr;
            idx += 1;
        }

        for (params_init, source_init, target_init) in reduction_rules_init {
            let root_ctx = metalogic.get_root_context();
            let mut params = SmallVec::with_capacity(params_init.len());
            for (name, type_str) in params_init.iter() {
                let param = root_ctx.with_locals(&params, |ctx| -> Result<Param, String> {
                    Ok(Param {
                        name: Some(Rc::new((*name).into())),
                        type_expr: Expr::parse(type_str, ctx)?,
                    })
                })?;
                params.push(param);
            }
            let body = root_ctx.with_locals(&params, |ctx| -> Result<ReductionBody, String> {
                let source = Expr::parse(source_init, ctx)?;
                let target = Expr::parse(target_init, ctx)?;
                Ok(ReductionBody { source, target })
            })?;
            let rule = ReductionRule { params, body };
            metalogic.reduction_rules.push(rule);
        }

        Ok(metalogic)
    }

    pub fn get_root_context(&self) -> MetaLogicContext {
        let globals = MetaLogicGlobals {
            metalogic: self,
            inhibit_reduction: false,
        };
        MetaLogicContext::with_globals(globals)
    }

    pub fn get_constant(&self, name: &str) -> Option<&Param> {
        let var_idx = self.constants.get_var_index(name, 0)?;
        Some(self.constants.get_var(var_idx))
    }

    pub fn parse_expr(&self, s: &str) -> Result<Expr, String> {
        Expr::parse(s, &self.get_root_context())
    }

    pub fn print_expr(&self, expr: &Expr) -> String {
        expr.print(&self.get_root_context())
    }

    pub fn reduce_expr(
        &self,
        expr: &mut Expr,
        convert_to_combinators: bool,
    ) -> Result<bool, String> {
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
        ctx.with_locals(&rule.params, |rule_ctx| {
            let source_type = rule.body.source.get_type(rule_ctx)?;
            let target_type = rule.body.target.get_type(rule_ctx)?;
            if source_type.compare(&target_type, rule_ctx) {
                Ok(())
            } else {
                let source_str = rule.body.source.print(rule_ctx);
                let source_type_str = source_type.print(rule_ctx);
                let target_str = rule.body.target.print(rule_ctx);
                let target_type_str = target_type.print(rule_ctx);
                Err(format!("type conflict in reduction rule between [{source_str} : {source_type_str}] and [{target_str} : {target_type_str}]"))
            }
        })
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
        if type_type.compare(&cmp_type_type, ctx) {
            Ok(())
        } else {
            let type_str = param.type_expr.print(ctx);
            let type_type_str = type_type.print(ctx);
            let cmp_type_type_str = cmp_type_type.print(ctx);
            Err(format!("parameter type [{type_str} : {type_type_str}] must have type [{cmp_type_type_str}] instead"))
        }
    }

    fn check_type_of_types_in_params(
        &self,
        params: &[Param],
        ctx: &MetaLogicContext,
    ) -> Result<(), String> {
        for param_idx in 0..params.len() {
            let param = &params[param_idx];
            ctx.with_locals(&params[0..param_idx], |param_ctx| {
                self.check_type_of_types_in_param(param, param_ctx)
            })?;
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
                ctx.with_local(&lambda.param, |body_ctx| {
                    self.check_type_of_types_in_expr(&lambda.body, body_ctx)
                })?;
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
        ctx.with_locals(&rule.params, |rule_ctx| {
            self.check_type_of_types_in_expr(&rule.body.source, rule_ctx)?;
            self.check_type_of_types_in_expr(&rule.body.target, rule_ctx)
        })
    }
}

#[derive(Clone, Copy)]
pub struct MetaLogicGlobals<'a> {
    pub metalogic: &'a MetaLogic,
    pub inhibit_reduction: bool,
}

impl VarAccessor<Param> for MetaLogicGlobals<'_> {
    fn get_var(&self, idx: VarIndex) -> &Param {
        self.metalogic.constants.get_var(idx)
    }

    fn for_each_var<R>(&self, f: impl FnMut(VarIndex, &Param) -> Option<R>) -> Option<R> {
        self.metalogic.constants.for_each_var(f)
    }
}

pub type MetaLogicContext<'a> = ParamContextImpl<Param, MetaLogicGlobals<'a>>;

impl MetaLogicContext<'_> {
    pub fn reduction_rules(&self) -> &[ReductionRule] {
        &self.globals().metalogic.reduction_rules
    }

    pub fn lambda_handler(&self) -> &dyn LambdaHandler {
        self.globals().metalogic.lambda_handler.as_ref()
    }

    pub fn with_inner_reduction_only<R>(&self, f: impl FnOnce(&Self) -> R) -> R {
        let new_globals = MetaLogicGlobals {
            inhibit_reduction: true,
            ..*self.globals()
        };
        self.with_new_globals(new_globals, f)
    }
}

/// We distinguish between comparisons with or without reductions by passing either
/// `MetaLogicContext` or `MinimalContext`.
pub trait ComparisonContext: ParamContext<Param> {
    fn with_reduction_options(
        &self,
        f: impl FnMut(ReductionOptionParam<Self>) -> bool,
        prefer_red: bool,
    ) -> bool;
}

// We need this so that with_reduction_options can take a single closure instead of two, which is
// necessary because we would need to mutate the same variable in both closures.
pub enum ReductionOptionParam<'a, 'b, Ctx: ComparisonContext> {
    NoRed(&'a Ctx),
    Red(&'a MetaLogicContext<'b>),
}

impl ComparisonContext for MinimalContext {
    fn with_reduction_options(
        &self,
        mut f: impl FnMut(ReductionOptionParam<Self>) -> bool,
        _: bool,
    ) -> bool {
        f(ReductionOptionParam::NoRed(self))
    }
}

impl ComparisonContext for MetaLogicContext<'_> {
    fn with_reduction_options(
        &self,
        mut f: impl FnMut(ReductionOptionParam<Self>) -> bool,
        prefer_red: bool,
    ) -> bool {
        let globals = self.globals();
        if globals.inhibit_reduction {
            // inhibit_reduction should affect exactly one call to with_reduction_options, so we
            // need to pass a new context to no_red where inhibit_reduction is set to false again.
            let new_globals = MetaLogicGlobals {
                inhibit_reduction: false,
                ..*globals
            };
            self.with_new_globals(new_globals, |new_ctx| {
                f(ReductionOptionParam::NoRed(new_ctx))
            })
        } else {
            if !prefer_red && f(ReductionOptionParam::NoRed(self)) {
                return true;
            }
            f(ReductionOptionParam::Red(self))
        }
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

    fn get_indep_type(
        &self,
        domain: Expr,
        codomain: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<Expr, String>;

    fn get_prop_type(&self, domain: Expr, ctx: MinimalContext) -> Result<Expr, String> {
        self.get_indep_type(
            domain,
            self.get_universe_type()?,
            DependentTypeCtorKind::Pi,
            ctx,
        )
    }

    fn get_dep_type(
        &self,
        domain: Expr,
        prop: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<Expr, String>;

    fn get_semi_generic_indep_type(
        &self,
        mut domain: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<(Param, Expr), String> {
        let codomain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let indep_type = ctx.with_local(&codomain_param, |subctx| {
            domain.shift_to_subcontext(&ctx, subctx);
            let codomain_var = Expr::var(-1);
            self.get_indep_type(domain, codomain_var, kind, *subctx)
        })?;
        Ok((codomain_param, indep_type))
    }

    fn get_semi_generic_dep_type(
        &self,
        mut domain: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<(Param, Expr), String> {
        let prop_param = Param {
            name: None,
            type_expr: self.get_prop_type(domain.clone(), ctx)?,
        };
        let dep_type = ctx.with_local(&prop_param, |subctx| {
            domain.shift_to_subcontext(&ctx, subctx);
            let prop_var = Expr::var(-1);
            self.get_dep_type(domain, prop_var, kind, *subctx)
        })?;
        Ok((prop_param, dep_type))
    }

    fn get_generic_indep_type(
        &self,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Expr), String> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let (codomain_param, indep_type) = ctx.with_local(&domain_param, |subctx| {
            let domain_var = Expr::var(-1);
            self.get_semi_generic_indep_type(domain_var, kind, *subctx)
        })?;
        Ok((domain_param, codomain_param, indep_type))
    }

    fn get_generic_dep_type(
        &self,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Expr), String> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let (prop_param, dep_type) = ctx.with_local(&domain_param, |subctx| {
            let domain_var = Expr::var(-1);
            self.get_semi_generic_dep_type(domain_var, kind, *subctx)
        })?;
        Ok((domain_param, prop_param, dep_type))
    }

    fn get_id_cmb(&self, domain: Expr, ctx: MinimalContext) -> Result<Expr, String>;

    fn get_const_cmb(
        &self,
        domain: Expr,
        codomain: Expr,
        ctx: MinimalContext,
    ) -> Result<Expr, String>;

    fn get_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        prop2: Expr,
        ctx: MinimalContext,
    ) -> Result<Expr, String>;
}

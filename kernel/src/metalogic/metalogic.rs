use std::{fmt::Debug, rc::Rc};

use anyhow::{anyhow, Error, Result};

use super::{expr::*, parse::*, print::*};

use crate::{
    generic::{context::*, context_object::*, expr_parts::*},
    util::{anyhow::*, parser::*},
};

#[derive(Clone)]
pub struct DefInit<'a> {
    pub sym: &'a str,
    pub red: &'a [&'a str],
}

pub struct MetaLogic {
    constants: Vec<Constant>,
    lambda_handler: Box<dyn LambdaHandler>,
    pub root_ctx_options: MetaLogicContextOptions,
}

impl MetaLogic {
    pub fn construct<F>(constants_init: &[DefInit], create_lambda_handler: F) -> Result<Self>
    where
        F: FnOnce(&[Param]) -> Box<dyn LambdaHandler>,
    {
        let mut constants = Vec::with_capacity(constants_init.len());
        for constant_init in constants_init {
            let mut parser_input = ParserInput(constant_init.sym);
            if let Some(name) = parser_input.try_read_name() {
                constants.push(Param {
                    name: Some(Rc::new(name.into())),
                    type_expr: Expr::default(),
                    implicit: false,
                });
            } else {
                return parser_input.expected("identifier");
            }
        }

        let lambda_handler = create_lambda_handler(&constants);

        let mut metalogic = MetaLogic {
            constants: constants
                .into_iter()
                .map(|param| Constant {
                    param,
                    reduction_rules: Vec::new(),
                })
                .collect(),
            lambda_handler,
            root_ctx_options: MetaLogicContextOptions {
                reduce_with_reduction_rules: false,
                reduce_with_combinators: false,
                print_all_implicit_args: true,
            },
        };

        let mut idx = 0;
        for constant_init in constants_init {
            let param = ParsingContext::parse(
                constant_init.sym,
                &metalogic.get_root_context(),
                |parsing_context| parsing_context.parse_param(),
            )?;
            metalogic.constants[idx].param.type_expr = param.type_expr;
            idx += 1;
        }

        idx = 0;
        for constant_init in constants_init {
            for rule_init in constant_init.red {
                let rule = ParsingContext::parse(
                    rule_init,
                    &metalogic.get_root_context(),
                    |parsing_context| parsing_context.parse_reduction_rule(idx as VarIndex),
                )
                .with_prefix(|| {
                    let name = metalogic.constants[idx].get_name_or_placeholder();
                    format!("failed to parse reduction rule for «{name}»")
                })?;
                metalogic.constants[idx].reduction_rules.push(rule);
            }
            idx += 1;
        }

        metalogic.insert_implicit_args()?;
        metalogic.fill_placeholders()?;

        metalogic.root_ctx_options.reduce_with_reduction_rules = true;
        metalogic.root_ctx_options.reduce_with_combinators = true;
        metalogic.root_ctx_options.print_all_implicit_args = false;
        Ok(metalogic)
    }

    pub fn get_root_context(&self) -> MetaLogicContext {
        self.get_root_context_with_options(self.root_ctx_options)
    }

    pub fn get_root_context_with_options(
        &self,
        options: MetaLogicContextOptions,
    ) -> MetaLogicContext {
        MetaLogicContext::with_globals(MetaLogicContextGlobals {
            metalogic: self,
            options,
        })
    }

    pub fn get_constant(&self, name: &str) -> Option<&Param> {
        let var_idx = self.constants.get_var_index(name, 0)?;
        Some(&self.constants.get_var(var_idx).param)
    }

    fn visit_exprs<Visitor: MetaLogicVisitor>(&self, visitor: &Visitor) -> Result<()> {
        let mut errors = Vec::new();
        let root_ctx = self.get_root_context();

        for constant in &self.constants {
            if let Err(error) = visitor.param(&constant.param, &root_ctx).with_prefix(|| {
                let name = constant.get_name_or_placeholder();
                visitor.get_constant_error_prefix(name)
            }) {
                errors.push(error);
            }

            for rule in &constant.reduction_rules {
                if let Err(error) = visitor.reduction_rule(rule, &root_ctx).with_prefix(|| {
                    let name = constant.get_name_or_placeholder();
                    let rule_str = rule.print(&root_ctx);
                    visitor.get_rule_error_prefix(name, &rule_str)
                }) {
                    errors.push(error);
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.combine())
        }
    }

    fn manipulate_exprs<Manipulator: MetaLogicManipulator>(
        &mut self,
        manipulator: &mut Manipulator,
    ) -> Result<()> {
        // Manipulate all types first, then all reduction rules in a second step, as manipulation
        // relies on accurate types.
        self.manipulate_constants(|constant, root_ctx, errors| {
            if let Err(error) = manipulator
                .param(&mut constant.param, &root_ctx)
                .with_prefix(|| {
                    let name = constant.get_name_or_placeholder();
                    manipulator.get_constant_error_prefix(name)
                })
            {
                errors.push(error);
            }
        })?;

        self.manipulate_constants(|constant, root_ctx, errors| {
            let name = constant.get_name_or_placeholder().to_owned();

            for rule in &mut constant.reduction_rules {
                if let Err(error) = manipulator.reduction_rule(rule, &root_ctx).with_prefix(|| {
                    let rule_str = rule.print(&root_ctx);
                    manipulator.get_rule_error_prefix(&name, &rule_str)
                }) {
                    errors.push(error);
                }
            }
        })
    }

    fn manipulate_constants(
        &mut self,
        mut f: impl FnMut(&mut Constant, &MetaLogicContext, &mut Vec<Error>),
    ) -> Result<()> {
        let mut errors = Vec::new();
        let mut new_constants = self.constants.clone();
        let root_ctx = self.get_root_context();

        for constant in &mut new_constants {
            f(constant, &root_ctx, &mut errors);
        }

        if errors.is_empty() {
            self.constants = new_constants;
            Ok(())
        } else {
            Err(errors.combine())
        }
    }

    fn insert_implicit_args(&mut self) -> Result<()> {
        self.manipulate_exprs(&mut ImplicitArgInserter {
            max_depth: self.lambda_handler.implicit_arg_max_depth(),
        })
    }

    fn fill_placeholders(&mut self) -> Result<()> {
        // Run two placeholder filling passes, to improve "unfilled placeholder" messages.
        let mut placeholder_filler = PlaceholderFiller {
            max_reduction_depth: self.lambda_handler.placeholder_max_reduction_depth(),
            force: false,
            has_unfilled_placeholders: false,
        };
        self.manipulate_exprs(&mut placeholder_filler)?;

        if placeholder_filler.has_unfilled_placeholders {
            placeholder_filler.force = true;
            placeholder_filler.has_unfilled_placeholders = false;
            self.manipulate_exprs(&mut placeholder_filler)?;
        }

        Ok(())
    }

    pub fn check_type_of_types(&self) -> Result<()> {
        self.visit_exprs(&DeepExprVisitor(ParamTypeChecker))
    }

    pub fn check_reduction_rule_types(&self) -> Result<()> {
        let mut errors = Vec::new();
        let root_ctx = self.get_root_context();

        for constant in &self.constants {
            for rule in &constant.reduction_rules {
                if let Err(error) =
                    self.check_reduction_rule_type(rule, &root_ctx)
                        .with_prefix(|| {
                            let name = constant.param.get_name_or_placeholder();
                            let rule_str = rule.print(&root_ctx);
                            format!("error in reduction rule for «{name}» («{rule_str}»)")
                        })
                {
                    errors.push(error);
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.combine())
        }
    }

    fn check_reduction_rule_type(
        &self,
        rule: &ReductionRule,
        ctx: &MetaLogicContext,
    ) -> Result<()> {
        ctx.with_locals(&rule.params, |rule_ctx| {
            //let mut clone = rule.body.source.clone();
            //clone.convert_to_combinators(rule_ctx, -1)?;
            //dbg!(clone.print(rule_ctx));
            let source_type = rule.body.source.get_type(rule_ctx)?;
            let target_type = rule.body.target.get_type(rule_ctx)?;
            if source_type.compare(&target_type, rule_ctx)? {
                Ok(())
            } else {
                let source_str = rule.body.source.print(rule_ctx);
                let source_type_str = source_type.print(rule_ctx);
                let target_str = rule.body.target.print(rule_ctx);
                let target_type_str = target_type.print(rule_ctx);
                Err(anyhow!("type conflict between «{source_str} : {source_type_str}»\nand «{target_str} : {target_type_str}»"))
            }
        })
    }
}

#[derive(Clone)]
pub struct Constant {
    pub param: Param,
    pub reduction_rules: Vec<ReductionRule>,
}

impl NamedObject for Constant {
    fn get_name(&self) -> Option<&str> {
        self.param.get_name()
    }
}

pub type ReductionRule = MultiLambda<Param, ReductionBody>;

impl ReductionRule {
    pub fn print(&self, ctx: &MetaLogicContext) -> String {
        let mut result = String::new();
        PrintingContext::print(&mut result, ctx, |printing_context| {
            printing_context.print_reduction_rule(&self)
        })
        .unwrap();
        result
    }
}

#[derive(Clone)]
pub struct ReductionBody {
    pub source: Expr,
    pub target: Expr,
    pub source_app_len: usize,
}

#[derive(Clone, Copy)]
pub struct MetaLogicContextOptions {
    pub reduce_with_reduction_rules: bool,
    pub reduce_with_combinators: bool,
    pub print_all_implicit_args: bool,
}

#[derive(Clone, Copy)]
pub struct MetaLogicContextGlobals<'a> {
    metalogic: &'a MetaLogic,
    options: MetaLogicContextOptions,
}

impl VarAccessor<Param> for MetaLogicContextGlobals<'_> {
    fn get_var(&self, idx: VarIndex) -> &Param {
        &self.metalogic.constants.get_var(idx).param
    }

    fn for_each_var<R>(&self, mut f: impl FnMut(VarIndex, &Param) -> Option<R>) -> Option<R> {
        self.metalogic
            .constants
            .for_each_var(|var_idx, constant| f(var_idx, &constant.param))
    }
}

pub type MetaLogicContext<'a> = ParamContextImpl<Param, MetaLogicContextGlobals<'a>>;

impl MetaLogicContext<'_> {
    pub fn metalogic(&self) -> &MetaLogic {
        self.globals().metalogic
    }

    pub fn options(&self) -> &MetaLogicContextOptions {
        &self.globals().options
    }

    pub fn constants(&self) -> &[Constant] {
        &self.metalogic().constants
    }

    pub fn lambda_handler(&self) -> &dyn LambdaHandler {
        self.metalogic().lambda_handler.as_ref()
    }

    pub fn with_new_options<R>(
        &self,
        options: MetaLogicContextOptions,
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        let globals = MetaLogicContextGlobals {
            options,
            ..*self.globals()
        };
        self.with_new_globals(globals, f)
    }
}

/// We distinguish between comparisons with or without reductions by passing either
/// `MetaLogicContext` or `MinimalContext`.
pub trait ComparisonContext: ParamContext<Param> {
    fn as_metalogic_context(&self) -> Option<&MetaLogicContext>;

    fn use_combinators(&self) -> bool;
}

// We need this so that with_reduction_options can take a single closure instead of two, which is
// necessary because we would need to mutate the same variable in both closures.
pub enum ReductionOptionParam<'a, 'b, Ctx: ComparisonContext> {
    NoRed(&'a Ctx),
    Red(&'a MetaLogicContext<'b>),
}

impl ComparisonContext for MinimalContext {
    fn as_metalogic_context(&self) -> Option<&MetaLogicContext> {
        None
    }

    fn use_combinators(&self) -> bool {
        false
    }
}

impl ComparisonContext for MetaLogicContext<'_> {
    fn as_metalogic_context(&self) -> Option<&MetaLogicContext> {
        Some(self)
    }

    fn use_combinators(&self) -> bool {
        self.globals().options.reduce_with_combinators
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum DependentTypeCtorKind {
    Pi,
    Sigma,
}

pub trait LambdaHandler {
    fn get_universe_type(&self) -> Result<Expr>;

    fn get_indep_type(
        &self,
        domain: Expr,
        codomain: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<Expr> {
        self.get_dep_type(
            domain.clone(),
            Expr::const_lambda(domain, codomain, &ctx),
            kind,
            ctx,
        )
    }

    fn get_prop_type(&self, domain: Expr, ctx: MinimalContext) -> Result<Expr> {
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
    ) -> Result<Expr>;

    fn get_semi_generic_indep_type(
        &self,
        mut domain: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<(Param, Expr)> {
        let codomain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
            implicit: false,
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
    ) -> Result<(Param, Expr)> {
        let prop_param = Param {
            name: None,
            type_expr: self.get_prop_type(domain.clone(), ctx)?,
            implicit: false,
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
    ) -> Result<(Param, Param, Expr)> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
            implicit: false,
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
    ) -> Result<(Param, Param, Expr)> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
            implicit: true,
        };
        let (prop_param, dep_type) = ctx.with_local(&domain_param, |subctx| {
            let domain_var = Expr::var(-1);
            self.get_semi_generic_dep_type(domain_var, kind, *subctx)
        })?;
        Ok((domain_param, prop_param, dep_type))
    }

    fn get_id_cmb(&self, domain: Expr, ctx: MinimalContext) -> Result<Expr>;

    fn get_const_cmb(&self, domain: Expr, codomain: Expr, ctx: MinimalContext) -> Result<Expr>;

    fn get_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        rel2: Expr,
        ctx: MinimalContext,
    ) -> Result<Expr>;

    fn get_indep_eq_type(
        &self,
        domain: Expr,
        left: Expr,
        right: Expr,
        ctx: MinimalContext,
    ) -> Result<Expr>;

    fn get_dep_eq_type(
        &self,
        left_domain: Expr,
        right_domain: Expr,
        domain_eq: Expr,
        left: Expr,
        right: Expr,
        ctx: MinimalContext,
    ) -> Result<Expr>;

    fn get_semi_generic_indep_eq_type(
        &self,
        mut domain: Expr,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Expr)> {
        let params = [
            Param {
                name: None,
                type_expr: domain.clone(),
                implicit: false,
            },
            Param {
                name: None,
                type_expr: domain.shifted_impl(ctx.locals_start(), 0, -1),
                implicit: false,
            },
        ];
        let eq_type = ctx.with_locals(&params, |subctx| {
            domain.shift_to_subcontext(&ctx, subctx);
            let left_var = Expr::var(-2);
            let right_var = Expr::var(-1);
            self.get_indep_eq_type(domain, left_var, right_var, *subctx)
        })?;
        let [left_param, right_param] = params;
        Ok((left_param, right_param, eq_type))
    }

    fn get_generic_indep_eq_type(
        &self,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Param, Expr)> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
            implicit: true,
        };
        let (left_param, right_param, eq_type) = ctx.with_local(&domain_param, |subctx| {
            let domain_var = Expr::var(-1);
            self.get_semi_generic_indep_eq_type(domain_var, *subctx)
        })?;
        Ok((domain_param, left_param, right_param, eq_type))
    }

    fn get_semi_generic_dep_eq_type(
        &self,
        mut left_domain: Expr,
        mut right_domain: Expr,
        mut domain_eq: Expr,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Expr)> {
        let params = [
            Param {
                name: None,
                type_expr: left_domain.clone(),
                implicit: false,
            },
            Param {
                name: None,
                type_expr: right_domain.shifted_impl(ctx.locals_start(), 0, -1),
                implicit: false,
            },
        ];
        let eq_type = ctx.with_locals(&params, |subctx| {
            left_domain.shift_to_subcontext(&ctx, subctx);
            right_domain.shift_to_subcontext(&ctx, subctx);
            domain_eq.shift_to_subcontext(&ctx, subctx);
            let left_var = Expr::var(-2);
            let right_var = Expr::var(-1);
            self.get_dep_eq_type(
                left_domain,
                right_domain,
                domain_eq,
                left_var,
                right_var,
                *subctx,
            )
        })?;
        let [left_param, right_param] = params;
        Ok((left_param, right_param, eq_type))
    }

    fn get_generic_dep_eq_type(
        &self,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Param, Param, Param, Expr)> {
        let params = [
            Param {
                name: None,
                type_expr: self.get_universe_type()?,
                implicit: true,
            },
            Param {
                name: None,
                type_expr: self.get_universe_type()?,
                implicit: true,
            },
            Param {
                name: None,
                type_expr: self.get_indep_eq_type(
                    self.get_universe_type()?,
                    Expr::var(-2),
                    Expr::var(-1),
                    ctx,
                )?,
                implicit: false,
            },
        ];
        let (left_param, right_param, eq_type) = ctx.with_locals(&params, |subctx| {
            let left_domain_var = Expr::var(-3);
            let right_domain_var = Expr::var(-2);
            let domain_eq_var = Expr::var(-1);
            self.get_semi_generic_dep_eq_type(
                left_domain_var,
                right_domain_var,
                domain_eq_var,
                *subctx,
            )
        })?;
        let [left_domain_param, right_domain_param, domain_eq_param] = params;
        Ok((
            left_domain_param,
            right_domain_param,
            domain_eq_param,
            left_param,
            right_param,
            eq_type,
        ))
    }

    fn implicit_arg_max_depth(&self) -> u32;
    fn placeholder_max_reduction_depth(&self) -> u32;
}

pub trait MetaLogicVisitorBase {
    fn get_constant_error_prefix(&self, name: &str) -> String;
    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String;
}

impl<Visitor: MetaLogicVisitorBase + ExprVisitor> MetaLogicVisitorBase
    for DeepExprVisitor<Visitor>
{
    fn get_constant_error_prefix(&self, name: &str) -> String {
        self.0.get_constant_error_prefix(name)
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        self.0.get_rule_error_prefix(name, rule_str)
    }
}

impl MetaLogicVisitorBase for ParamTypeChecker {
    fn get_constant_error_prefix(&self, name: &str) -> String {
        format!("type of constant «{name}» is invalid")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("types within reduction rule for «{name}» are invalid («{rule_str}»)")
    }
}

impl MetaLogicVisitorBase for ImplicitArgInserter {
    fn get_constant_error_prefix(&self, name: &str) -> String {
        format!("invalid implicit arguments in type of constant «{name}»")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("invalid implicit arguments in reduction rule for «{name}» («{rule_str}»)")
    }
}

impl MetaLogicVisitorBase for PlaceholderFiller {
    fn get_constant_error_prefix(&self, name: &str) -> String {
        format!("unable to fill placeholder in type of constant «{name}»")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("unable to fill placeholder in reduction rule for «{name}» («{rule_str}»)")
    }
}

pub trait MetaLogicVisitor: MetaLogicVisitorBase + ExprVisitor {
    fn reduction_rule(&self, _rule: &ReductionRule, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_body(&self, _body: &ReductionBody, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

impl<Visitor: MetaLogicVisitorBase + ExprVisitor> MetaLogicVisitor for DeepExprVisitor<Visitor> {
    fn reduction_rule(&self, rule: &ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        self.params(&rule.params, ctx)?;
        ctx.with_locals(&rule.params, |body| self.reduction_body(&rule.body, body))
    }

    fn reduction_body(&self, body: &ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&body.source, ctx)?;
        self.expr(&body.target, ctx)
    }
}

pub trait MetaLogicManipulator: MetaLogicVisitorBase + ExprManipulator {
    fn reduction_rule(&mut self, _rule: &mut ReductionRule, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_body(&mut self, _body: &mut ReductionBody, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

impl MetaLogicManipulator for ImplicitArgInserter {
    fn reduction_rule(&mut self, rule: &mut ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        self.params(&mut rule.params, ctx)?;
        ctx.with_locals(&rule.params, |body| {
            self.reduction_body(&mut rule.body, body)
        })
    }

    fn reduction_body(&mut self, body: &mut ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        let source_type = self.insert_implicit_args_and_get_type(&mut body.source, ctx)?;
        let target_type = self.insert_implicit_args_and_get_type(&mut body.target, ctx)?;

        let (_, source_app_len) = body.source.get_app_info();
        body.source_app_len = source_app_len;

        Expr::check_type_arg_implicitness(&source_type, &target_type, ctx)
    }
}

impl MetaLogicManipulator for PlaceholderFiller {
    fn reduction_rule(&mut self, rule: &mut ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        self.params(&mut rule.params, ctx)?;
        ctx.with_locals(&rule.params, |body| {
            self.reduction_body(&mut rule.body, body)
        })
    }

    fn reduction_body(&mut self, body: &mut ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        let source_type = self.fill_placeholders(&mut body.source, Expr::Placeholder, ctx)?;
        self.fill_placeholders(&mut body.target, source_type, ctx)?;
        Ok(())
    }
}

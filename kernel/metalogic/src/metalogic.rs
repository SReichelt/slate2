use std::{
    collections::HashMap,
    sync::atomic::{AtomicBool, Ordering},
};

use anyhow::{anyhow, Error, Result};
use log::{trace, warn};
use rayon::prelude::*;
use smallvec::SmallVec;
use symbol_table::{Symbol, SymbolTable};

use slate_kernel_generic::{context::*, context_object::*, expr_parts::*};
use slate_kernel_util::{anyhow::*, parser::*};

use crate::{
    expr::*, expr_manipulators::*, expr_visitors::*, metalogic_context::*,
    metalogic_manipulators::*, metalogic_visitors::*, parse::*, print::*,
};

pub struct ConstInit<'a> {
    pub sym: &'a str,
    pub red: &'a [&'a str],
}

impl ConstInit<'_> {
    fn for_each_name(&self, mut f: impl FnMut(&str)) -> Result<()> {
        f(Self::extract_name(self.sym)?);
        for rule_init in self.red {
            f(Self::extract_name(rule_init)?);
        }
        Ok(())
    }

    fn extract_name(sym: &str) -> Result<&str> {
        let mut parser_input = ParserInput(sym);
        if let Some(name) = parser_input.try_read_name() {
            Ok(name)
        } else {
            parser_input.expected("identifier")
        }
    }

    fn parse_params(&self, metalogic: &mut MetaLogic) -> Result<()> {
        let const_idx = Self::parse_constant(self.sym, metalogic)?;
        for rule_init in self.red {
            let (rule_name, rule) = ParsingContext::parse(
                rule_init,
                &metalogic.get_root_context(),
                |parsing_context| parsing_context.parse_named_reduction_rule(const_idx),
            )?;
            Self::apply_reduction_rule(&rule_name, rule, metalogic, const_idx)?;
        }
        Ok(())
    }

    fn parse_constant(sym: &str, metalogic: &mut MetaLogic) -> Result<VarIndex> {
        let param = ParsingContext::parse(sym, &metalogic.get_root_context(), |parsing_context| {
            parsing_context.parse_param()
        })?;
        let idx = metalogic.get_var_index(param.name, 0).unwrap();
        metalogic.constants[idx as usize].param.type_expr = param.type_expr;
        Ok(idx)
    }

    fn apply_reduction_rule(
        rule_name: &str,
        mut rule: ReductionRule,
        metalogic: &mut MetaLogic,
        const_idx: VarIndex,
    ) -> Result<()> {
        let idx = metalogic.get_constant_index(rule_name).unwrap();
        metalogic.constants[idx as usize].param.type_expr =
            rule.get_eq_type(&metalogic.get_root_context())?;
        Self::set_reduction_rule_eq(&mut rule, idx);
        metalogic.constants[const_idx as usize]
            .reduction_rules
            .push(rule);
        Ok(())
    }

    fn set_reduction_rule_eq(rule: &mut ReductionRule, idx: VarIndex) {
        let mut param_args: SmallVec<[Arg; INLINE_PARAMS]> =
            SmallVec::with_capacity(rule.params.len());
        let mut param_idx = -(rule.params.len() as VarIndex);
        for param in &rule.params {
            param_args.push(Arg {
                expr: Expr::var(param_idx),
                implicit: param.implicit,
                match_all: false,
            });
            param_idx += 1;
        }
        rule.body.eq = Expr::dyn_multi_app(Expr::var(idx), param_args);
    }
}

pub struct MetaLogic {
    symbol_table: SymbolTable,
    constants: Vec<Constant>,
    config: MetaLogicConfig,
    pub root_ctx_options: MetaLogicContextOptions,
}

impl MetaLogic {
    pub fn construct<F>(constants_init: &[&ConstInit], get_config: F) -> Result<Self>
    where
        F: FnOnce(&HashMap<String, VarIndex>) -> MetaLogicConfig,
    {
        let symbol_table = SymbolTable::new();

        let mut constants = Vec::new();
        let mut constants_map = HashMap::new();
        let mut idx = 0;
        for constant_init in constants_init {
            constant_init.for_each_name(|name| {
                constants.push(Param {
                    name: Some(symbol_table.intern(name)),
                    type_expr: Expr::default(),
                    implicit: false,
                });
                constants_map.insert(name.to_owned(), idx);
                idx += 1;
            })?;
        }

        let config = get_config(&constants_map);

        let mut metalogic = MetaLogic {
            symbol_table,
            constants: constants
                .into_iter()
                .map(|param| Constant {
                    param,
                    reduction_rules: Vec::new(),
                })
                .collect(),
            config,
            root_ctx_options: MetaLogicContextOptions {
                reduce_with_reduction_rules: false,
                reduce_with_combinators: false,
                print_all_implicit_args: true,
            },
        };

        for constant_init in constants_init {
            constant_init.parse_params(&mut metalogic)?;
        }

        metalogic.insert_implicit_args()?;

        metalogic.root_ctx_options.reduce_with_reduction_rules = true;

        metalogic.fill_placeholders()?;
        metalogic.reduce_reduction_rule_args()?;

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
        MetaLogicContext::new(MetaLogicContextData {
            metalogic: self,
            options,
        })
    }

    pub fn get_constants(&self) -> &[Constant] {
        &self.constants
    }

    pub fn get_constant_index(&self, name: &str) -> Option<VarIndex> {
        let symbol = self.symbol_table.intern(name);
        self.constants.get_var_index(Some(symbol), 0)
    }

    pub fn get_constant(&self, name: &str) -> Option<&Constant> {
        let var_idx = self.get_constant_index(name)?;
        Some(self.constants.get_var(var_idx))
    }

    pub fn get_display_name(&self, obj: &impl NamedObject<Option<Symbol>>) -> &str {
        if let Some(name) = obj.get_name() {
            self.symbol_table.resolve(name)
        } else {
            "_"
        }
    }

    fn visit_exprs<Visitor: MetaLogicVisitor>(&self, visitor: &Visitor) -> Result<()> {
        let root_ctx = self.get_root_context();

        let errors: Vec<Error> = self
            .constants
            .par_iter()
            .flat_map(|constant| {
                let mut errors = Vec::new();
                let name = self.get_display_name(constant);

                trace_start(&visitor.get_constant_title(name));
                if let Err(error) = visitor.constant(constant, &root_ctx).with_prefix(|| {
                    let param_str = constant.param.print(&root_ctx);
                    visitor.get_constant_error_prefix(name, &param_str)
                }) {
                    errors.push(error);
                }
                trace_end(&visitor.get_constant_title(name));

                trace_start(&visitor.get_rules_title(name));
                for rule in &constant.reduction_rules {
                    if let Err(error) = visitor.reduction_rule(rule, &root_ctx).with_prefix(|| {
                        let rule_str = rule.print(&root_ctx);
                        visitor.get_rule_error_prefix(name, &rule_str)
                    }) {
                        errors.push(error);
                    }
                }
                trace_end(&visitor.get_rules_title(name));

                errors
            })
            .collect();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.combine())
        }
    }

    fn manipulate_exprs<Manipulator: MetaLogicManipulator>(
        &mut self,
        manipulator: &Manipulator,
    ) -> Result<()> {
        // Manipulate all types first, then all reduction rules in a second step, as manipulation
        // relies on accurate types.
        self.constants = self.manipulate_constants(|constant, root_ctx, errors| {
            let name = self.get_display_name(constant);

            trace_start(&manipulator.get_constant_title(name));
            if let Err(error) = manipulator.constant(constant, root_ctx).with_prefix(|| {
                let param_str = constant.param.print(root_ctx);
                manipulator.get_constant_error_prefix(name, &param_str)
            }) {
                errors.push(error);
            }
            trace_end(&manipulator.get_constant_title(name));
        })?;

        self.constants = self.manipulate_constants(|constant, root_ctx, errors| {
            let name = self.get_display_name(constant);

            trace_start(&manipulator.get_rules_title(name));
            for rule in &mut constant.reduction_rules {
                if let Err(error) = manipulator.reduction_rule(rule, root_ctx).with_prefix(|| {
                    let rule_str = rule.print(root_ctx);
                    manipulator.get_rule_error_prefix(name, &rule_str)
                }) {
                    errors.push(error);
                }
            }
            trace_end(&manipulator.get_rules_title(name));
        })?;

        Ok(())
    }

    fn manipulate_constants(
        &self,
        f: impl Fn(&mut Constant, &MetaLogicContext, &mut Vec<Error>) + Sync,
    ) -> Result<Vec<Constant>> {
        let mut new_constants = self.constants.clone();
        let root_ctx = self.get_root_context();

        let errors: Vec<Error> = new_constants
            .par_iter_mut()
            .flat_map(|constant| {
                let mut errors = Vec::new();
                f(constant, &root_ctx, &mut errors);
                errors
            })
            .collect();

        if errors.is_empty() {
            Ok(new_constants)
        } else {
            Err(errors.combine())
        }
    }

    fn insert_implicit_args(&mut self) -> Result<()> {
        self.manipulate_exprs(&ImplicitArgInserter {
            max_depth: self.config.implicit_arg_max_depth,
        })
    }

    fn fill_placeholders(&mut self) -> Result<()> {
        // Run two placeholder filling passes, to improve "unfilled placeholder" messages.
        let mut placeholder_filler = PlaceholderFiller {
            max_reduction_depth: self.config.placeholder_max_reduction_depth,
            force: false,
            match_var_ctx: None,
            has_unfilled_placeholders: AtomicBool::new(false),
        };
        self.manipulate_exprs(&placeholder_filler)?;

        if placeholder_filler
            .has_unfilled_placeholders
            .load(Ordering::Relaxed)
        {
            warn!("second placeholder filling pass needed");
            placeholder_filler.force = true;
            placeholder_filler
                .has_unfilled_placeholders
                .store(false, Ordering::Relaxed);
            self.manipulate_exprs(&placeholder_filler)?;
        }

        Ok(())
    }

    fn reduce_reduction_rule_args(&mut self) -> Result<()> {
        let orig_reduce_with_reduction_rules = self.root_ctx_options.reduce_with_reduction_rules;
        self.root_ctx_options.reduce_with_reduction_rules = true;
        let result = self.manipulate_exprs(&ReductionRuleArgReducer);
        self.root_ctx_options.reduce_with_reduction_rules = orig_reduce_with_reduction_rules;
        result
    }

    pub fn check_type_of_types(&self) -> Result<()> {
        self.visit_exprs(&DeepExprVisitor(ParamTypeChecker))
    }

    pub fn check_reduction_rule_types(&self) -> Result<()> {
        self.visit_exprs(&ReductionRuleChecker)
    }

    pub fn parse_expr(&self, s: &str) -> Result<Expr> {
        let root_ctx = self.get_root_context();

        let mut expr = Expr::parse(s, &root_ctx)?;

        let arg_inserter = ImplicitArgInserter {
            max_depth: self.config.implicit_arg_max_depth,
        };
        arg_inserter.insert_implicit_args(&mut expr, &root_ctx)?;

        self.adapt_user_expr(&mut expr)?;

        Ok(expr)
    }

    pub fn add_definition(&mut self, name: &str, mut value: Expr) -> Result<&Param> {
        let value_type = self.adapt_user_expr(&mut value)?;

        let idx = self.constants.len();
        self.constants.push(Constant {
            param: Param {
                name: Some(self.symbol_table.intern(name)),
                type_expr: value_type.clone(),
                implicit: false,
            },
            reduction_rules: vec![ReductionRule {
                params: SmallVec::new(),
                body: ReductionBody {
                    domain: value_type.clone(),
                    source: Expr::var(idx as VarIndex),
                    target: value.clone(),
                    source_app_len: 0,
                    eq: Expr::var(idx as VarIndex + 1),
                },
            }],
        });
        self.constants.push(Constant {
            param: Param {
                name: Some(self.symbol_table.intern(&format!("{name}_def"))),
                type_expr: self.config.get_indep_eq_type(
                    value_type,
                    Expr::var(idx as VarIndex),
                    value,
                )?,
                implicit: false,
            },
            reduction_rules: Vec::new(),
        });

        let reduction_rule_checker = ReductionRuleChecker;
        if let Err(err) =
            reduction_rule_checker.constant(&self.constants[idx], &self.get_root_context())
        {
            self.constants.truncate(idx);
            return Err(err);
        }

        Ok(&self.constants[idx].param)
    }

    fn adapt_user_expr(&self, expr: &mut Expr) -> Result<Expr> {
        let root_ctx = self.get_root_context();

        let placeholder_filler = PlaceholderFiller {
            max_reduction_depth: self.config.placeholder_max_reduction_depth,
            force: true,
            match_var_ctx: None,
            has_unfilled_placeholders: AtomicBool::new(false),
        };
        let expr_type = placeholder_filler.fill_placeholders(expr, Expr::Placeholder, &root_ctx)?;

        let param_type_checker = DeepExprVisitor(ParamTypeChecker);
        param_type_checker.expr(expr, &root_ctx)?;

        Ok(expr_type)
    }
}

impl VarAccessor<Param> for MetaLogic {
    fn get_var(&self, idx: VarIndex) -> &Param {
        &self.constants.get_var(idx).param
    }

    fn for_each_var<R>(&self, mut f: impl FnMut(VarIndex, &Param) -> Option<R>) -> Option<R> {
        self.constants
            .for_each_var(|var_idx, constant| f(var_idx, &constant.param))
    }
}

pub trait MetaLogicRef {
    fn metalogic(&self) -> &MetaLogic;

    fn constants(&self) -> &[Constant] {
        &self.metalogic().constants
    }

    fn config(&self) -> &MetaLogicConfig {
        &self.metalogic().config
    }

    fn get_named_var_index(&self, name: &str, occurrence: usize) -> Option<VarIndex>
    where
        Self: NamedVarAccessor<Option<Symbol>, Param>,
    {
        let symbol = self.metalogic().symbol_table.intern(name);
        self.get_var_index(Some(symbol), occurrence)
    }

    fn get_display_name(&self, param: &Param) -> &str {
        self.metalogic().get_display_name(param)
    }

    fn intern_name(&self, name: &str) -> Symbol {
        self.metalogic().symbol_table.intern(name)
    }
}

#[derive(Clone)]
pub struct Constant {
    pub param: Param,
    pub reduction_rules: Vec<ReductionRule>,
}

impl NamedObject<Option<Symbol>> for Constant {
    fn get_name(&self) -> Option<Symbol> {
        self.param.get_name()
    }
}

pub type ReductionRule = MultiLambda<Param, ReductionBody>;

pub trait IsReductionRule {
    fn get_eq_type(&self, ctx: &MetaLogicContext) -> Result<Expr>;
}

impl IsReductionRule for ReductionRule {
    /*fn from_eq(var_idx: VarIndex, mut eq: Expr, ctx: &MetaLogicContext) -> Result<Self> {
        let mut type_expr = eq.get_type(ctx)?;
        let mut params = SmallVec::new();
        loop {
            if let Some(lambda) = ctx.with_locals(&params, |params_ctx| {
                let lambda = type_expr.match_dep_type_as_lambda(
                    StandardTypeCtorKind::Pi,
                    true,
                    params_ctx,
                )?;
                params_ctx.with_local(&lambda.param, |lambda_param_ctx| {
                    eq.shift_to_subcontext(params_ctx, lambda_param_ctx);
                    eq = take(&mut eq).apply(
                        Arg {
                            expr: Expr::var(-1),
                            implicit: lambda.param.implicit,
                            match_all: false,
                        },
                        lambda_param_ctx,
                    );
                });
                Some(lambda)
            }) {
                params.push(lambda.param.clone());
                type_expr = lambda.body;
            } else {
                break;
            }
        }

        if let Some((domain, source, target)) = ctx.with_locals(&params, |params_ctx| {
            type_expr.match_indep_eq_type(params_ctx)
        }) {
            if let Some((source_var_idx, source_app_len)) = source.get_const_app_info() {
                if source_var_idx == var_idx {
                    Ok(ReductionRule {
                        params,
                        body: ReductionBody {
                            domain: domain.clone(),
                            source: source.clone(),
                            target: target.clone(),
                            source_app_len,
                            eq,
                        },
                    })
                } else {
                    Err(anyhow!(
                        "source of reduction rule must refer to corresponding constant"
                    ))
                }
            } else {
                Err(anyhow!(
                    "source of reduction rule must be a constant application"
                ))
            }
        } else {
            Err(anyhow!("reduction rule must refer to an equality"))
        }
    }*/

    fn get_eq_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        let mut eq_type = self.body.get_eq_type(ctx)?;
        for param in self.params.iter().rev() {
            eq_type = ctx.config().get_dep_type(
                param.type_expr.clone(),
                Expr::lambda(param.clone(), eq_type),
                StandardTypeCtorKind::Pi,
            )?;
        }
        Ok(eq_type)
    }
}

impl CanPrint for ReductionRule {
    fn print(&self, ctx: &MetaLogicContext) -> String {
        let mut result = String::new();
        PrintingContext::print(&mut result, ctx, |printing_context| {
            printing_context.print_reduction_rule(self)
        })
        .unwrap();
        result
    }
}

#[derive(Clone)]
pub struct ReductionBody {
    pub domain: Expr,
    pub source: Expr,
    pub target: Expr,
    pub source_app_len: usize,
    pub eq: Expr,
}

impl ReductionBody {
    fn get_eq_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        ctx.config().get_indep_eq_type(
            self.domain.clone(),
            self.source.clone(),
            self.target.clone(),
        )
    }
}

pub struct MetaLogicConfig {
    pub universe_type: Expr,

    pub fun_ctor: Expr,
    pub pi_ctor: Expr,

    pub id_cmb: Expr,
    pub const_cmb: Expr,
    pub subst_cmb: Expr,
    pub substd_cmb: Expr,

    pub pair_ctor: Expr,
    pub sigma_ctor: Expr,

    pub eq_ctor: Expr,
    pub eqd_ctor: Expr,

    pub refl_eq: Expr,
    pub symm_eq: Expr,
    pub symmd_eq: Expr,
    pub trans_eq: Expr,
    pub transd_eq: Expr,

    pub implicit_arg_max_depth: u32,
    pub placeholder_max_reduction_depth: u32,
}

impl MetaLogicConfig {
    pub fn get_indep_ctor(&self, kind: StandardTypeCtorKind) -> &Expr {
        match kind {
            StandardTypeCtorKind::Pi => &self.fun_ctor,
            StandardTypeCtorKind::Sigma => &self.pair_ctor,
        }
    }

    pub fn get_dep_ctor(&self, kind: StandardTypeCtorKind) -> &Expr {
        match kind {
            StandardTypeCtorKind::Pi => &self.pi_ctor,
            StandardTypeCtorKind::Sigma => &self.sigma_ctor,
        }
    }

    pub fn get_indep_type(
        &self,
        domain: Expr,
        codomain: Expr,
        kind: StandardTypeCtorKind,
    ) -> Result<Expr> {
        let ctor = self.get_indep_ctor(kind);
        if ctor.is_empty() {
            return Err(anyhow!("specified type not defined"));
        }
        Ok(Expr::multi_app(
            ctor.clone(),
            [Arg::explicit(domain), Arg::explicit(codomain)],
        ))
    }

    pub fn get_prop_type(&self, domain: Expr) -> Result<Expr> {
        self.get_indep_type(domain, self.universe_type.clone(), StandardTypeCtorKind::Pi)
    }

    pub fn get_dep_type(
        &self,
        domain: Expr,
        prop: Expr,
        kind: StandardTypeCtorKind,
    ) -> Result<Expr> {
        let ctor = self.get_dep_ctor(kind);
        if ctor.is_empty() {
            return Err(anyhow!("specified dependent type not defined"));
        }
        Ok(Expr::multi_app(
            ctor.clone(),
            [Arg::implicit(domain), Arg::explicit(prop)],
        ))
    }

    pub fn get_indep_eq_type(&self, domain: Expr, left: Expr, right: Expr) -> Result<Expr> {
        if self.eq_ctor.is_empty() {
            return Err(anyhow!("equality type not defined"));
        }
        Ok(Expr::multi_app(
            self.eq_ctor.clone(),
            [
                Arg::implicit(domain),
                Arg::explicit(left),
                Arg::explicit(right),
            ],
        ))
    }

    pub fn get_dep_eq_type(
        &self,
        left_domain: Expr,
        right_domain: Expr,
        domain_eq: Expr,
        left: Expr,
        right: Expr,
    ) -> Result<Expr> {
        if self.eqd_ctor.is_empty() {
            return Err(anyhow!("dependent equality type not defined"));
        }
        Ok(Expr::multi_app(
            self.eqd_ctor.clone(),
            [
                Arg::implicit(left_domain),
                Arg::implicit(right_domain),
                Arg::explicit(domain_eq),
                Arg::explicit(left),
                Arg::explicit(right),
            ],
        ))
    }
}

pub trait MetaLogicVisitorBase: Sync {
    fn get_constant_title(&self, name: &str) -> Option<String>;
    fn get_rules_title(&self, name: &str) -> Option<String>;

    fn get_constant_error_prefix(&self, name: &str, param_str: &str) -> String;
    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String;
}

fn trace_start(title: &Option<String>) {
    if let Some(title_str) = title {
        trace!("{title_str}: start");
    }
}

fn trace_end(title: &Option<String>) {
    if let Some(title_str) = title {
        trace!("{title_str}: end");
    }
}

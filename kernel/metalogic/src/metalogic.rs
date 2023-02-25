use std::{
    borrow::Cow,
    collections::HashMap,
    fmt::Debug,
    sync::atomic::{AtomicBool, Ordering},
};

use anyhow::{Error, Result};
use log::{trace, warn};
use rayon::prelude::*;
use smallvec::SmallVec;
use symbol_table::{Symbol, SymbolTable};

use slate_kernel_generic::{context::*, expr_parts::*};
use slate_kernel_util::{anyhow::*, parser::*};

use crate::{
    expr::*, expr_manipulators::*, expr_visitors::*, metalogic_context::*,
    metalogic_manipulators::*, metalogic_visitors::*, parse::*, print::*,
};

#[derive(Clone)]
pub struct DefInit<'a> {
    pub sym: &'a str,
    pub red: &'a [&'a str],
}

pub struct MetaLogic {
    symbol_table: SymbolTable,
    constants: Vec<Constant>,
    lambda_handler: Box<dyn LambdaHandler>,
    pub root_ctx_options: MetaLogicContextOptions,
}

impl MetaLogic {
    pub fn construct<F>(constants_init: &[Cow<DefInit>], create_lambda_handler: F) -> Result<Self>
    where
        F: FnOnce(&HashMap<&str, VarIndex>) -> Box<dyn LambdaHandler>,
    {
        let symbol_table = SymbolTable::new();

        let mut constants = Vec::with_capacity(constants_init.len());
        let mut constants_map = HashMap::with_capacity(constants_init.len());
        let mut idx = 0;
        for constant_init in constants_init {
            let mut parser_input = ParserInput(constant_init.sym);
            if let Some(name) = parser_input.try_read_name() {
                constants.push(Param {
                    name: Some(symbol_table.intern(name)),
                    type_expr: Expr::default(),
                    implicit: false,
                });
                constants_map.insert(name, idx);
                idx += 1;
            } else {
                return parser_input.expected("identifier");
            }
        }

        let lambda_handler = create_lambda_handler(&constants_map);

        let mut metalogic = MetaLogic {
            symbol_table,
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
                    let name = metalogic.get_display_name(&metalogic.constants[idx]);
                    format!("failed to parse reduction rule for «{name}»")
                })?;
                metalogic.constants[idx].reduction_rules.push(rule);
            }
            idx += 1;
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

    pub fn get_constant(&self, name: &str) -> Option<&Constant> {
        let symbol = self.symbol_table.intern(name);
        let var_idx = self.constants.get_var_index(symbol, 0)?;
        Some(self.constants.get_var(var_idx))
    }

    pub fn get_display_name(&self, obj: &impl NamedObject<Symbol>) -> &str {
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
            max_depth: self.lambda_handler.implicit_arg_max_depth(),
        })
    }

    fn fill_placeholders(&mut self) -> Result<()> {
        // Run two placeholder filling passes, to improve "unfilled placeholder" messages.
        let mut placeholder_filler = PlaceholderFiller {
            max_reduction_depth: self.lambda_handler.placeholder_max_reduction_depth(),
            force: false,
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
            max_depth: self.lambda_handler.implicit_arg_max_depth(),
        };
        arg_inserter.expr(&mut expr, &root_ctx)?;

        self.adapt_user_expr(&mut expr)?;

        Ok(expr)
    }

    pub fn add_definition(&mut self, name: &str, mut value: Expr) -> Result<&Param> {
        let value_type = self.adapt_user_expr(&mut value)?;

        let idx = self.constants.len();
        self.constants.push(Constant {
            param: Param {
                name: Some(self.symbol_table.intern(name)),
                type_expr: value_type,
                implicit: false,
            },
            reduction_rules: vec![ReductionRule {
                params: SmallVec::new(),
                body: ReductionBody {
                    source: Expr::var(idx as VarIndex),
                    target: value,
                    source_app_len: 0,
                },
            }],
        });

        let reduction_rule_checker = ReductionRuleChecker;
        if let Err(err) =
            reduction_rule_checker.constant(&self.constants[idx], &self.get_root_context())
        {
            self.constants.pop();
            return Err(err);
        }

        Ok(&self.constants[idx].param)
    }

    fn adapt_user_expr(&self, expr: &mut Expr) -> Result<Expr> {
        let root_ctx = self.get_root_context();

        let placeholder_filler = PlaceholderFiller {
            max_reduction_depth: self.lambda_handler.placeholder_max_reduction_depth(),
            force: true,
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

    fn lambda_handler(&self) -> &dyn LambdaHandler {
        self.metalogic().lambda_handler.as_ref()
    }

    fn get_named_var_index(&self, name: &str, occurrence: usize) -> Option<VarIndex>
    where
        Self: NamedVarAccessor<Symbol, Param>,
    {
        let symbol = self.metalogic().symbol_table.intern(name);
        self.get_var_index(symbol, occurrence)
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

impl NamedObject<Symbol> for Constant {
    fn get_name(&self) -> Option<Symbol> {
        self.param.get_name()
    }
}

pub type ReductionRule = MultiLambda<Param, ReductionBody>;

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
    pub source: Expr,
    pub target: Expr,
    pub source_app_len: usize,
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum DependentTypeCtorKind {
    Pi,
    Sigma,
}

pub trait LambdaHandler: Sync {
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

    fn get_generic_indep_type(
        &self,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Expr)> {
        let params = [
            Param {
                name: None,
                type_expr: self.get_universe_type()?,
                implicit: false,
            },
            Param {
                name: None,
                type_expr: self.get_universe_type()?,
                implicit: false,
            },
        ];
        let indep_type = ctx.with_locals(&params, |subctx| {
            let domain_var = Expr::var(-2);
            let codomain_var = Expr::var(-1);
            self.get_indep_type(domain_var, codomain_var, kind, *subctx)
        })?;
        let [domain_param, codomain_param] = params;
        Ok((domain_param, codomain_param, indep_type))
    }

    fn get_generic_dep_type(
        &self,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Expr)> {
        let params = [
            Param {
                name: None,
                type_expr: self.get_universe_type()?,
                implicit: true,
            },
            Param {
                name: None,
                type_expr: Expr::var(-1),
                implicit: false,
            },
        ];
        let dep_type = ctx.with_locals(&params, |subctx| {
            let domain_var = Expr::var(-2);
            let prop_var = Expr::var(-1);
            self.get_dep_type(domain_var, prop_var, kind, *subctx)
        })?;
        let [domain_param, prop_param] = params;
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

    fn get_generic_indep_eq_type(
        &self,
        ctx: MinimalContext,
    ) -> Result<(Param, Param, Param, Expr)> {
        let params = [
            Param {
                name: None,
                type_expr: self.get_universe_type()?,
                implicit: true,
            },
            Param {
                name: None,
                type_expr: Expr::var(-1),
                implicit: false,
            },
            Param {
                name: None,
                type_expr: Expr::var(-2),
                implicit: false,
            },
        ];
        let eq_type = ctx.with_locals(&params, |subctx| {
            let domain_var = Expr::var(-3);
            let left_var = Expr::var(-2);
            let right_var = Expr::var(-1);
            self.get_indep_eq_type(domain_var, left_var, right_var, *subctx)
        })?;
        let [domain_param, left_param, right_param] = params;
        Ok((domain_param, left_param, right_param, eq_type))
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
            Param {
                name: None,
                type_expr: Expr::var(-3),
                implicit: false,
            },
            Param {
                name: None,
                type_expr: Expr::var(-3),
                implicit: false,
            },
        ];
        let eq_type = ctx.with_locals(&params, |subctx| {
            let left_domain_var = Expr::var(-5);
            let right_domain_var = Expr::var(-4);
            let domain_eq_var = Expr::var(-3);
            let left_var = Expr::var(-2);
            let right_var = Expr::var(-1);
            self.get_dep_eq_type(
                left_domain_var,
                right_domain_var,
                domain_eq_var,
                left_var,
                right_var,
                *subctx,
            )
        })?;
        let [left_domain_param, right_domain_param, domain_eq_param, left_param, right_param] =
            params;
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

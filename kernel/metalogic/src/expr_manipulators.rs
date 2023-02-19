use std::{
    mem::take,
    sync::atomic::{AtomicBool, Ordering},
};

use anyhow::{anyhow, Result};
use log::info;
use smallvec::SmallVec;

use slate_kernel_generic::{context::*, context_object::*, expr_parts::*};

use crate::{expr::*, metalogic::*, metalogic_context::*};

pub trait ExprManipulator {
    fn expr(&self, _expr: &mut Expr, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn param(&self, _param: &mut Param, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn params(&self, params: &mut [Param], ctx: &MetaLogicContext) -> Result<()> {
        for param_idx in 0..params.len() {
            let (prev, next) = params.split_at_mut(param_idx);
            let param = &mut next[0];
            ctx.with_locals(prev, |param_ctx| self.param(param, param_ctx))?;
        }
        Ok(())
    }

    fn arg(&self, _arg: &mut Arg, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

pub struct ImplicitArgInserter {
    pub max_depth: u32,
}

impl ImplicitArgInserter {
    pub fn insert_implicit_args_and_get_type(
        &self,
        expr: &mut Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        let mut expr_type = self.insert_implicit_args(expr, ctx)?;
        if self.max_depth > 0 && expr_type != Expr::Placeholder {
            let type_arg_inserter = ImplicitArgInserter {
                max_depth: self.max_depth - 1,
            };
            type_arg_inserter.insert_implicit_args(&mut expr_type, ctx)?;
            return Ok(expr_type);
        }
        Ok(Expr::Placeholder)
    }

    pub fn insert_implicit_args(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<Expr> {
        match expr {
            Expr::Placeholder => Ok(Expr::Placeholder),
            Expr::Var(var) => var.get_type(ctx),
            Expr::App(app) => {
                let fun = &mut app.body;
                let arg = &mut app.param;
                let mut fun_type = self.insert_implicit_args_and_get_type(fun, ctx)?;
                self.arg(arg, ctx)?;
                while let Some(lambda) =
                    fun_type.match_generic_dep_type_as_lambda(DependentTypeCtorKind::Pi, true, ctx)
                {
                    if lambda.param.implicit && !arg.implicit {
                        *fun = Expr::app(
                            take(fun),
                            Arg {
                                expr: Expr::Placeholder,
                                implicit: true,
                                match_all: false,
                            },
                        );
                        fun_type = lambda.apply(arg.clone(), ctx);
                    } else if arg.implicit && !lambda.param.implicit {
                        let name = ctx.get_display_name(&lambda.param);
                        return Err(anyhow!("expected explicit argument for «{name}»"));
                    } else {
                        return Ok(lambda.apply(arg.clone(), ctx));
                    }
                }
                Ok(Expr::Placeholder)
            }
            Expr::Lambda(lambda) => {
                self.param(&mut lambda.param, ctx)?;
                ctx.with_local(&lambda.param, |body_ctx| {
                    let body_type =
                        self.insert_implicit_args_and_get_type(&mut lambda.body, body_ctx)?;
                    Expr::get_fun_type(&lambda.param, body_type, ctx)
                })
            }
        }
    }
}

impl ExprManipulator for ImplicitArgInserter {
    fn expr(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<()> {
        self.insert_implicit_args(expr, ctx)?;
        Ok(())
    }

    fn param(&self, param: &mut Param, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&mut param.type_expr, ctx)
    }

    fn arg(&self, arg: &mut Arg, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&mut arg.expr, ctx)
    }
}

pub struct PlaceholderFiller {
    pub max_reduction_depth: u32,
    pub force: bool,
    pub has_unfilled_placeholders: AtomicBool,
}

impl PlaceholderFiller {
    pub fn try_fill_placeholders(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<Expr> {
        let sub_filler = PlaceholderFiller {
            max_reduction_depth: self.max_reduction_depth,
            force: false,
            has_unfilled_placeholders: AtomicBool::new(false),
        };
        sub_filler.fill_placeholders(expr, Expr::Placeholder, ctx)
    }

    pub fn fill_placeholders(
        &self,
        expr: &mut Expr,
        mut expected_type: Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        self.fill_arg_placeholders(expr, &mut expected_type, ctx)?;
        self.fill_inner_placeholders(expr, expected_type, ctx)
    }

    fn fill_inner_placeholders(
        &self,
        expr: &mut Expr,
        mut expected_type: Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        match expr {
            Expr::Placeholder => {
                self.has_unfilled_placeholders
                    .store(true, Ordering::Relaxed);
                if self.force {
                    let type_str_options = MetaLogicContextOptions {
                        reduce_with_reduction_rules: true,
                        reduce_with_combinators: true,
                        print_all_implicit_args: false,
                    };
                    ctx.with_new_options(type_str_options, |type_str_ctx| {
                        let type_str = expected_type.print(type_str_ctx);
                        if let Ok(true) = expected_type.reduce_all(type_str_ctx) {
                            let reduced_type_str = expected_type.print(type_str_ctx);
                            if reduced_type_str != type_str {
                                return Err(anyhow!("unfilled placeholder of type «{type_str}»\n(reduced: «{reduced_type_str}»)"));
                            }
                        }
                        Err(anyhow!("unfilled placeholder of type «{type_str}»"))
                    })
                } else {
                    Ok(expected_type)
                }
            }
            Expr::Var(var) => {
                let var_type = var.get_type(ctx)?;
                if var_type.is_empty() {
                    Ok(expected_type)
                } else {
                    Ok(var_type)
                }
            }
            Expr::App(app) => {
                let fun = &mut app.body;
                let arg = &mut app.param;

                let initial_arg_type = self.try_fill_placeholders(&mut arg.expr, ctx)?;
                let initial_fun_type = self.fill_arg_placeholders_in_fun(
                    fun,
                    arg,
                    expected_type,
                    initial_arg_type,
                    ctx,
                )?;

                let fun_type_result = self.fill_inner_placeholders(fun, initial_fun_type, ctx);
                // Report errors in arguments first, to better support the "underscore trick".
                let (mut fun_type, fun_type_err) = match fun_type_result {
                    Ok(fun_type) => (fun_type, Ok(())),
                    Err(err) => (self.try_fill_placeholders(fun, ctx)?, Err(err)),
                };
                //dbg!(
                //    "start",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    expected_type.print(ctx),
                //    initial_fun_type.print(ctx)
                //);
                let lambda = self.get_fun_type_lambda(&mut fun_type, arg.implicit, ctx)?;
                //dbg!(
                //    "fill arg placeholders",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    fun_type.print(ctx),
                //    lambda.param.type_expr.print(ctx)
                //);
                self.fill_placeholders(&mut arg.expr, lambda.param.type_expr.clone(), ctx)?;
                //dbg!(
                //    "filled arg placeholders",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    fun_type.print(ctx),
                //    arg_type.print(ctx),
                //);
                fun_type_err?;
                Ok(lambda.apply(arg.clone(), ctx))
            }
            Expr::Lambda(lambda) => {
                let expected_type_lambda =
                    self.get_fun_type_lambda(&mut expected_type, lambda.param.implicit, ctx)?;
                if lambda.param.type_expr.is_empty() {
                    if self.force {
                        info!(
                            "unfilled parameter type in last pass: {}",
                            lambda.param.print(ctx)
                        );
                    }
                    lambda.param.type_expr = expected_type_lambda.param.type_expr;
                }
                self.param(&mut lambda.param, ctx)?;
                ctx.with_local(&lambda.param, |body_ctx| {
                    let body_type = self.fill_placeholders(
                        &mut lambda.body,
                        expected_type_lambda.body,
                        body_ctx,
                    )?;
                    Expr::get_fun_type(&lambda.param, body_type, ctx)
                })
            }
        }
    }

    fn fill_arg_placeholders(
        &self,
        expr: &mut Expr,
        expected_type: &mut Expr,
        ctx: &MetaLogicContext,
    ) -> Result<bool> {
        if expected_type.is_empty() || !matches!(expr, Expr::App(_)) {
            return Ok(true);
        }

        let mut params = SmallVec::new();
        let mut args = SmallVec::new();
        let mut has_unfilled_args = false;
        let innermost_fun_type =
            self.analyze_app(expr, ctx, &mut params, &mut args, &mut has_unfilled_args)?;

        if has_unfilled_args {
            if self.force {
                info!("unfilled arguments in last pass: {}", expr.print(ctx));
            }

            if ctx.with_locals(&params, |ctx_with_params| {
                //dbg!(
                //    "apply",
                //    fun.print(ctx),
                //    innermost_fun_type.print(ctx_with_params),
                //    expected_fun_type.print(ctx)
                //);
                innermost_fun_type.substitute_and_compare(
                    ctx_with_params,
                    &mut args,
                    expected_type,
                    ctx,
                )
            })? {
                Self::apply_args(expr, args, ctx);
                //dbg!("applied", fun.print(ctx));
            } else {
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn fill_arg_placeholders_in_fun(
        &self,
        fun: &mut Expr,
        arg: &mut Arg,
        expected_type: Expr,
        initial_arg_type: Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        let has_arg_type = !initial_arg_type.is_empty();
        let mut initial_fun_type = Self::get_expected_fun_type(
            fun,
            arg,
            &expected_type,
            initial_arg_type,
            arg.implicit,
            ctx,
        )?;

        if has_arg_type {
            if !self.fill_arg_placeholders(fun, &mut initial_fun_type, ctx)? {
                //dbg!(
                //    "compare fail",
                //    fun.print(ctx),
                //    fun_params
                //        .iter()
                //        .map(|param| param.get_name_or_placeholder())
                //        .collect::<Vec<&str>>(),
                //    ctx.with_locals(&fun_params, |ctx_with_params| innermost_fun_type
                //        .print(ctx_with_params)),
                //    expected_fun_type.print(ctx)
                //);
                if self.max_reduction_depth > 0 {
                    //dbg!("reduce");
                    let mut initial_arg_type = self.try_fill_placeholders(&mut arg.expr, ctx)?;
                    if initial_arg_type.apply_one_reduction_rule(ctx)? {
                        //dbg!(initial_arg_type.print(ctx));
                        let sub_filler = PlaceholderFiller {
                            max_reduction_depth: self.max_reduction_depth - 1,
                            force: self.force,
                            has_unfilled_placeholders: AtomicBool::new(false),
                        };
                        let result = sub_filler.fill_arg_placeholders_in_fun(
                            fun,
                            arg,
                            expected_type,
                            initial_arg_type,
                            ctx,
                        );
                        if sub_filler.has_unfilled_placeholders.load(Ordering::Relaxed) {
                            self.has_unfilled_placeholders
                                .store(true, Ordering::Relaxed);
                        }
                        initial_fun_type = result?;
                        //dbg!("result", fun.print(ctx), arg.expr.print(ctx));
                    }
                }
            }
        }

        Ok(initial_fun_type)
    }

    fn get_expected_fun_type(
        fun: &Expr,
        arg: &Arg,
        expected_type: &Expr,
        initial_arg_type: Expr,
        implicit: bool,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        let min_ctx = ctx.as_minimal();
        let mut expected_param = Param {
            name: None,
            type_expr: initial_arg_type.clone(),
            implicit,
        };
        let expected_body_type = if let Expr::Lambda(lambda) = fun {
            expected_param.name = lambda.param.name;
            // Replace all occurrences of `arg` in `expected_type` with the new variable.
            // This may or may not be what we want in a particular case, but heuristics are OK when
            // auto-filling placeholders.
            Self::replaced_or_shifted(expected_type, &min_ctx, &arg.expr, &min_ctx)?
        } else {
            Expr::Placeholder
        };
        ctx.lambda_handler().get_dep_type(
            initial_arg_type,
            Expr::lambda(expected_param, expected_body_type),
            DependentTypeCtorKind::Pi,
            min_ctx,
        )
    }

    /// Decomposes the type of the innermost function within `expr` (i.e. of the expression returned
    /// by `get_app_info`) into a telescope along with a body type in the context of that telescope.
    /// Also copies the corresponding argument expressions into `result_args`.
    /// Example: If we have `f : A → B → C`, then `analyze_app` of `f a b` yields `C` along with
    /// `result_params` of types `A` and `B`, and `result_args` `a` and `b`.
    fn analyze_app(
        &self,
        expr: &mut Expr,
        ctx: &MetaLogicContext,
        result_params: &mut SmallVec<[Param; INLINE_PARAMS]>,
        result_args: &mut SmallVec<[Expr; INLINE_PARAMS]>,
        has_unfilled_args: &mut bool,
    ) -> Result<Expr> {
        if let Expr::App(app) = expr {
            let fun = &mut app.body;
            let arg = &mut app.param;
            if arg.expr.is_empty() {
                *has_unfilled_args = true;
            }
            let mut fun_type =
                self.analyze_app(fun, ctx, result_params, result_args, has_unfilled_args)?;
            let lambda = ctx.with_locals(result_params, |fun_type_ctx| {
                self.get_fun_type_lambda(&mut fun_type, arg.implicit, fun_type_ctx)
            })?;
            result_params.push(lambda.param);
            result_args.push(arg.expr.clone());
            Ok(lambda.body)
        } else if *has_unfilled_args {
            self.try_fill_placeholders(expr, ctx)
        } else {
            // Skip unnecessary work if we don't have any arguments to fill.
            Ok(Expr::Placeholder)
        }
    }

    fn apply_args(
        mut expr: &mut Expr,
        mut args: SmallVec<[Expr; INLINE_PARAMS]>,
        ctx: &MetaLogicContext,
    ) {
        while let Expr::App(app) = expr {
            if let Some(mut value) = args.pop() {
                if app.param.expr != value {
                    if let Expr::App(value_app) = &mut value {
                        if let Some(beta_reduced) = value_app.beta_reduce(ctx) {
                            value = beta_reduced;
                        }
                    }
                    app.param.expr = value;
                }
                expr = &mut app.body;
            } else {
                break;
            }
        }
    }

    fn get_fun_type_lambda(
        &self,
        fun_type: &mut Expr,
        implicit: bool,
        ctx: &MetaLogicContext,
    ) -> Result<LambdaExpr> {
        fun_type.reduce(ctx, true, self.max_reduction_depth as i32)?;
        if let Some(lambda) =
            fun_type.match_generic_dep_type_as_lambda(DependentTypeCtorKind::Pi, true, ctx)
        {
            Ok(lambda)
        } else {
            Ok(LambdaExpr {
                param: Param {
                    name: None,
                    type_expr: Expr::Placeholder,
                    implicit,
                },
                body: Expr::Placeholder,
            })
        }
    }

    fn replaced_or_shifted<Ctx: ComparisonContext>(
        expr: &Expr,
        expr_ctx: &Ctx,
        match_expr: &Expr,
        match_superctx: &Ctx,
    ) -> Result<Expr> {
        let shift_end = match_superctx.subcontext_shift(expr_ctx);

        if match_expr.shift_and_compare(match_superctx, expr, expr_ctx)? {
            return Ok(Expr::var(shift_end - 1));
        }

        match expr {
            Expr::Placeholder => Ok(Expr::Placeholder),
            Expr::Var(var) => Ok(Expr::Var(var.shifted_impl(
                expr_ctx.locals_start(),
                shift_end,
                -1,
            ))),
            Expr::App(app) => Ok(Expr::App(Box::new(App {
                param: Arg {
                    expr: Self::replaced_or_shifted(
                        &app.param.expr,
                        expr_ctx,
                        match_expr,
                        match_superctx,
                    )?,
                    ..app.param
                },
                body: Self::replaced_or_shifted(&app.body, expr_ctx, match_expr, match_superctx)?,
            }))),
            Expr::Lambda(lambda) => {
                let param = Param {
                    type_expr: Self::replaced_or_shifted(
                        &lambda.param.type_expr,
                        expr_ctx,
                        match_expr,
                        match_superctx,
                    )?,
                    ..lambda.param
                };
                let body = expr_ctx.with_local(&param, |body_ctx| {
                    Self::replaced_or_shifted(&lambda.body, body_ctx, match_expr, match_superctx)
                })?;
                Ok(Expr::Lambda(Box::new(Lambda { param, body })))
            }
        }
    }
}

impl ExprManipulator for PlaceholderFiller {
    fn expr(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<()> {
        self.fill_placeholders(expr, Expr::Placeholder, ctx)?;
        Ok(())
    }

    fn param(&self, param: &mut Param, ctx: &MetaLogicContext) -> Result<()> {
        let expected_type = ctx.lambda_handler().get_universe_type()?;
        self.fill_placeholders(&mut param.type_expr, expected_type, ctx)?;
        Ok(())
    }

    fn arg(&self, arg: &mut Arg, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&mut arg.expr, ctx)
    }
}

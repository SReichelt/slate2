use std::{
    mem::take,
    sync::atomic::{AtomicBool, Ordering},
};

use anyhow::{anyhow, Result};
use log::info;

use slate_kernel_generic::{context::*, context_object::*, expr_parts::*};

use crate::{expr::*, metalogic::*, metalogic_context::*};

pub trait ExprManipulator {
    fn expr(&self, _expr: &mut Expr, _expected_type: Expr, _ctx: &MetaLogicContext) -> Result<()>;

    fn param(&self, param: &mut Param, ctx: &MetaLogicContext) -> Result<()> {
        let expected_type = ctx.config().universe_type.clone();
        self.expr(&mut param.type_expr, expected_type, ctx)
    }

    fn params(&self, params: &mut [Param], ctx: &MetaLogicContext) -> Result<()> {
        for param_idx in 0..params.len() {
            let (prev, next) = params.split_at_mut(param_idx);
            let param = &mut next[0];
            ctx.with_locals(prev, |param_ctx| self.param(param, param_ctx))?;
        }
        Ok(())
    }

    fn arg(&self, arg: &mut Arg, expected_type: Expr, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&mut arg.expr, expected_type, ctx)
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
                while let Some(lambda) =
                    fun_type.match_type_as_lambda(StandardTypeCtorKind::Pi, ctx)
                {
                    if lambda.param.implicit && !arg.implicit {
                        let inserted_arg = Arg::implicit(Expr::Placeholder);
                        *fun = Expr::app(take(fun), inserted_arg.clone());
                        fun_type = lambda.apply(inserted_arg, ctx);
                    } else if arg.implicit && !lambda.param.implicit {
                        let name = ctx.get_display_name(&lambda.param);
                        return Err(anyhow!("expected explicit argument for «{name}»"));
                    } else {
                        self.arg(arg, lambda.param.type_expr.clone(), ctx)?;
                        return Ok(lambda.apply(arg.clone(), ctx));
                    }
                }
                self.arg(arg, Expr::Placeholder, ctx)?;
                Ok(Expr::Placeholder)
            }
            Expr::Lambda(lambda) => {
                self.param(&mut lambda.param, ctx)?;
                ctx.with_local(&lambda.param, |body_ctx| {
                    let body_type =
                        self.insert_implicit_args_and_get_type(&mut lambda.body, body_ctx)?;
                    Expr::get_fun_type(&lambda.param, body_type, ctx, body_ctx)
                })
            }
            Expr::Cast(cast) => self.insert_implicit_args(&mut cast.expr, ctx),
        }
    }
}

impl ExprManipulator for ImplicitArgInserter {
    fn expr(&self, expr: &mut Expr, _expected_type: Expr, ctx: &MetaLogicContext) -> Result<()> {
        self.insert_implicit_args(expr, ctx)?;
        Ok(())
    }
}

pub struct PlaceholderFiller {
    pub max_reduction_depth: u32,
    pub force: bool,
    pub match_var_ctx: Option<MinimalContext>,
    pub has_unfilled_placeholders: AtomicBool,
}

impl PlaceholderFiller {
    pub fn try_fill_placeholders(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<Expr> {
        let sub_filler = PlaceholderFiller {
            force: false,
            has_unfilled_placeholders: AtomicBool::new(false),
            ..*self
        };
        let mut result_type = sub_filler.fill_placeholders(expr, Expr::Placeholder, ctx)?;
        if sub_filler.has_unfilled_placeholders.load(Ordering::Relaxed) {
            result_type = Expr::Placeholder;
        }
        Ok(result_type)
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
                        if let Ok(reductions) = expected_type.reduce_all(type_str_ctx) {
                            if !reductions.is_empty() {
                                let reduced_type_str = expected_type.print(type_str_ctx);
                                if reduced_type_str != type_str {
                                    return Err(anyhow!("unfilled placeholder of type «{type_str}»\n(reduced: «{reduced_type_str}»)"));
                                }
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

                //dbg!(
                //    "start",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    expected_type.print(ctx),
                //);

                let initial_arg_type = self.try_fill_placeholders(&mut arg.expr, ctx)?;
                //dbg!(
                //    "arg",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    initial_arg_type.print(ctx),
                //);
                let initial_fun_type = self.fill_arg_placeholders_in_fun(
                    fun,
                    arg,
                    expected_type,
                    initial_arg_type,
                    ctx,
                )?;
                //dbg!(
                //    "fun",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    initial_fun_type.print(ctx),
                //);

                let fun_type_result = self.fill_inner_placeholders(fun, initial_fun_type, ctx);
                // Report errors in arguments first, to better support the "underscore trick".
                let (mut fun_type, fun_type_err) = match fun_type_result {
                    Ok(fun_type) => (fun_type, Ok(())),
                    Err(err) => (self.try_fill_placeholders(fun, ctx)?, Err(err)),
                };
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
                //    lambda.param.type_expr.print(ctx),
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
                    Expr::get_fun_type(&lambda.param, body_type, ctx, body_ctx)
                })
            }
            Expr::Cast(cast) => self.fill_inner_placeholders(&mut cast.expr, expected_type, ctx),
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

        let mut params = InlineVec::new();
        let mut args = InlineVec::new();
        let mut has_unfilled_args = false;
        let result_type =
            self.analyze_app(expr, ctx, &mut params, &mut args, &mut has_unfilled_args)?;

        if has_unfilled_args {
            if self.force {
                info!("unfilled arguments in last pass: {}", expr.print(ctx));
            }

            if Self::match_app_expected_type(expected_type, &result_type, ctx, &params, &mut args)?
            {
                self.apply_args(expr, args, ctx);
                //dbg!("applied", expr.print(ctx));
            } else {
                //dbg!("compare fail", expr.print(ctx));
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
                if self.max_reduction_depth > 0 {
                    //dbg!("reduce");
                    let mut initial_arg_type = self.try_fill_placeholders(&mut arg.expr, ctx)?;
                    if initial_arg_type.apply_one_reduction_rule(ctx)? {
                        //dbg!(initial_arg_type.print(ctx));
                        let sub_filler = PlaceholderFiller {
                            max_reduction_depth: self.max_reduction_depth - 1,
                            has_unfilled_placeholders: AtomicBool::new(false),
                            ..*self
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
            type_expr: initial_arg_type,
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
        ctx.with_local(&expected_param, |body_ctx| {
            Expr::get_fun_type(&expected_param, expected_body_type, ctx, body_ctx)
        })
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
        result_params: &mut InlineVec<Param>,
        result_args: &mut InlineVec<Expr>,
        has_unfilled_args: &mut bool,
    ) -> Result<Expr> {
        if let Expr::App(app) = expr {
            let fun = &mut app.body;
            let arg = &app.param;
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

    fn match_app_expected_type(
        expected_type: &mut Expr,
        result_type: &Expr,
        ctx: &MetaLogicContext,
        params: &InlineVec<Param>,
        args: &mut InlineVec<Expr>,
    ) -> Result<bool> {
        ctx.with_locals(params, |ctx_with_params| {
            //dbg!(
            //    "apply",
            //    expr.print(ctx),
            //    params
            //        .iter()
            //        .map(|param| ctx.get_display_name(param))
            //        .collect::<Vec<&str>>(),
            //    result_type.print(ctx_with_params),
            //    expected_type.print(ctx),
            //);

            // When the expected type is a function type with known domain but unknown prop/codomain, we
            // declare it as a dependent function type, but the actual function type may be independent.
            // Adapt the expected type in that case, to make the match operation succeed.
            if let Some((expected_domain, _)) =
                expected_type.match_dep_type(StandardTypeCtorKind::Pi, ctx)
            {
                if result_type
                    .match_indep_type(StandardTypeCtorKind::Pi, ctx_with_params)
                    .is_some()
                {
                    *expected_type = ctx.config().get_indep_type(
                        expected_domain.clone(),
                        Expr::Placeholder,
                        StandardTypeCtorKind::Pi,
                    )?;
                }
            }

            result_type.substitute_and_compare(ctx_with_params, args, expected_type, ctx)
        })
    }

    fn apply_args(&self, mut expr: &mut Expr, mut args: InlineVec<Expr>, ctx: &MetaLogicContext) {
        while let Expr::App(app) = expr {
            if let Some(mut value) = args.pop() {
                if app.param.expr != value {
                    if let Expr::App(value_app) = &mut value {
                        if let Some(beta_reduced) = value_app.beta_reduce(ctx) {
                            value = beta_reduced;
                        }
                    }
                    if app.param.expr.is_empty() {
                        if let Some(match_var_ctx) = &self.match_var_ctx {
                            let is_match_var = if let Expr::Var(var) = &value {
                                var.valid_in_superctx(&ctx.as_minimal(), match_var_ctx)
                            } else {
                                false
                            };
                            if !is_match_var {
                                app.param.match_all = true;
                            }
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
        if let Some(lambda) = fun_type.match_type_as_lambda(StandardTypeCtorKind::Pi, ctx) {
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
            Expr::Cast(cast) => Ok(Expr::Cast(Box::new(CastExpr {
                expr: Self::replaced_or_shifted(&cast.expr, expr_ctx, match_expr, match_superctx)?,
                target_type: Self::replaced_or_shifted(
                    &cast.target_type,
                    expr_ctx,
                    match_expr,
                    match_superctx,
                )?,
                type_defeq: cast.type_defeq.clone(),
            }))),
        }
    }
}

impl ExprManipulator for PlaceholderFiller {
    fn expr(&self, expr: &mut Expr, expected_type: Expr, ctx: &MetaLogicContext) -> Result<()> {
        self.fill_placeholders(expr, expected_type, ctx)?;
        Ok(())
    }
}

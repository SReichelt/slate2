use std::{borrow::Cow, fmt};

use slate_kernel_generic::{context::*, expr_parts::*};
use smallvec::SmallVec;

use crate::{expr::*, metalogic::*, metalogic_context::*};

pub struct PrintingContext<'a, 'b, W: fmt::Write> {
    output: &'a mut W,
    context: &'a MetaLogicContext<'b>,
}

impl<W: fmt::Write> PrintingContext<'_, '_, W> {
    pub fn print(
        result: &mut W,
        ctx: &MetaLogicContext,
        f: impl FnOnce(&mut PrintingContext<W>) -> fmt::Result,
    ) -> fmt::Result {
        let mut printing_context = PrintingContext {
            output: result,
            context: ctx,
        };
        f(&mut printing_context)
    }

    pub fn print_expr(&mut self, expr: &Expr) -> fmt::Result {
        self.print_expr_with_parens(expr, false, false, false, false, false)
    }

    pub fn print_expr_with_parens(
        &mut self,
        expr: &Expr,
        parens_for_app: bool,
        parens_for_lambda: bool,
        parens_for_fun: bool,
        parens_for_prod: bool,
        parens_for_eq: bool,
    ) -> fmt::Result {
        if self.try_print_std_type_ctor(
            expr,
            StandardTypeCtorKind::Pi,
            'Π',
            '→',
            parens_for_lambda,
            parens_for_fun,
        )? {
            return Ok(());
        }

        if self.try_print_std_type_ctor(
            expr,
            StandardTypeCtorKind::Sigma,
            'Σ',
            '×',
            parens_for_lambda,
            parens_for_prod,
        )? {
            return Ok(());
        }

        if self.try_print_eq_ctor(expr, parens_for_eq)? {
            return Ok(());
        }

        match expr {
            Expr::Placeholder => self.output.write_char('_')?,
            Expr::Var(Var(idx)) => {
                let param = self.context.get_var(*idx);
                self.output
                    .write_str(self.context.get_display_name(param))?;
                let occurrence = self.context.get_name_occurrence(*idx, param);
                for _ in 0..occurrence {
                    self.output.write_char('⁺')?;
                }
            }
            Expr::App(app) => {
                let mut fun = &app.body;
                let arg = &app.param;

                if !arg.implicit && !self.context.options().print_all_implicit_args {
                    while let Expr::App(fun_app) = fun {
                        if fun_app.param.implicit {
                            fun = &fun_app.body;
                        } else {
                            break;
                        }
                    }
                }

                if self.try_print_let_binding(fun, arg, SmallVec::new(), parens_for_lambda)? {
                    return Ok(());
                }

                if parens_for_app {
                    self.output.write_char('(')?;
                }
                self.print_expr_with_parens(fun, false, true, true, true, true)?;
                self.output.write_char(' ')?;
                self.print_arg(arg, true)?;
                if parens_for_app {
                    self.output.write_char(')')?;
                }
            }
            Expr::Lambda(lambda) => {
                if parens_for_lambda {
                    self.output.write_char('(')?;
                }
                self.output.write_str("λ ")?;
                self.print_lambda(lambda)?;
                if parens_for_lambda {
                    self.output.write_char(')')?;
                }
            }
            Expr::Cast(cast) => {
                self.print_expr_with_parens(&cast.expr, true, true, true, true, true)?;
                self.output.write_str("↑")?;
            }
        }

        Ok(())
    }

    fn print_arg(&mut self, arg: &Arg, parens: bool) -> fmt::Result {
        if arg.implicit {
            self.output.write_char('{')?;
            if arg.match_all {
                self.output.write_char('{')?;
            }
            self.print_expr(&arg.expr)?;
            if arg.match_all {
                self.output.write_char('}')?;
            }
            self.output.write_char('}')?;
            Ok(())
        } else {
            self.print_expr_with_parens(&arg.expr, parens, parens, parens, parens, parens)
        }
    }

    fn disambiguate_param<'a>(&self, param: &'a Param) -> Cow<'a, Param> {
        let mut name = param.name;
        if name.is_some() && self.context.has_var(name) {
            let mut name_str = self.context.get_display_name(param).to_owned();
            if let Expr::Var(Var(type_idx)) = param.type_expr {
                let type_param = self.context.get_var(type_idx);
                let type_name = self.context.get_display_name(type_param);
                if type_name.len() == 1 && type_name.starts_with(|c| ('A'..'I').contains(&c)) {
                    name_str = type_name.to_lowercase();
                    name = Some(self.context.intern_name(&name_str));
                }
            }
            while self.context.has_var(name) {
                name_str += "\'";
                name = Some(self.context.intern_name(&name_str));
            }
            let mut new_param = param.clone();
            new_param.name = name;
            return Cow::Owned(new_param);
        }
        Cow::Borrowed(param)
    }

    fn print_lambda(&mut self, lambda: &LambdaExpr) -> fmt::Result {
        let param = self.disambiguate_param(&lambda.param);
        self.print_param(&param)?;
        self.output.write_str(". ")?;
        self.context.with_local(&param, |body_ctx| {
            let mut body_printing_ctx = PrintingContext {
                output: self.output,
                context: body_ctx,
            };
            body_printing_ctx.print_expr(&lambda.body)
        })
    }

    /// If the expression is a multi-lambda abstraction applied to the corresponding number of
    /// arguments, print it as a let-binding followed by the body.
    fn try_print_let_binding<'a>(
        &mut self,
        fun: &'a Expr,
        arg: &'a Arg,
        mut outer_args: SmallVec<[&'a Arg; INLINE_PARAMS]>,
        parens_for_lambda: bool,
    ) -> Result<bool, fmt::Error> {
        outer_args.push(arg);

        // Check for a nested let-binding.
        if let Expr::App(app) = fun {
            self.try_print_let_binding(&app.body, &app.param, outer_args, parens_for_lambda)
        } else {
            // Not nested further. Now check if we have the appropriate number of lambda
            // abstractions inside, collecting their parameters, and print it if we do.
            self.try_print_let_binding_inner(fun, SmallVec::new(), &outer_args, parens_for_lambda)
        }
    }

    fn try_print_let_binding_inner<'a>(
        &mut self,
        body: &'a Expr,
        mut params: SmallVec<[&'a Param; INLINE_PARAMS]>,
        args: &SmallVec<[&Arg; INLINE_PARAMS]>,
        parens_for_lambda: bool,
    ) -> Result<bool, fmt::Error> {
        if params.len() == args.len() {
            if parens_for_lambda {
                self.output.write_char('(')?;
            }
            self.output.write_char('[')?;
            self.print_let_binding_inner(body, SmallVec::new(), &params, args)?;
            if parens_for_lambda {
                self.output.write_char(')')?;
            }
            return Ok(true);
        } else if let Expr::Lambda(lambda) = body {
            params.push(&lambda.param);
            return self.try_print_let_binding_inner(&lambda.body, params, args, parens_for_lambda);
        }

        Ok(false)
    }

    fn print_let_binding_inner(
        &mut self,
        body: &Expr,
        mut outer_params: SmallVec<[Param; INLINE_PARAMS]>,
        params: &[&Param],
        args: &[&Arg],
    ) -> fmt::Result {
        let (orig_param, params_rest) = params.split_first().unwrap();
        let param = self.disambiguate_param(orig_param);
        self.context.with_locals(&outer_params, |param_ctx| {
            let mut param_printing_ctx = PrintingContext {
                output: self.output,
                context: param_ctx,
            };
            param_printing_ctx.print_param(&param)
        })?;
        self.output.write_str(" ⫽ ")?;
        let (arg, args_rest) = args.split_last().unwrap();
        self.print_arg(arg, false)?;
        outer_params.push(param.into_owned());
        if params_rest.is_empty() {
            self.output.write_char(']')?;
            self.output.write_char(' ')?;
            self.context.with_locals(&outer_params, |body_ctx| {
                let mut body_printing_ctx = PrintingContext {
                    output: self.output,
                    context: body_ctx,
                };
                body_printing_ctx.print_expr(body)
            })
        } else {
            self.output.write_str("; ")?;
            self.print_let_binding_inner(body, outer_params, params_rest, args_rest)
        }
    }

    pub fn print_param(&mut self, param: &Param) -> fmt::Result {
        if param.implicit {
            self.output.write_char('{')?;
        }
        self.output
            .write_str(self.context.get_display_name(param))?;
        self.output.write_str(" : ")?;
        self.print_expr_with_parens(&param.type_expr, false, true, false, false, false)?;
        if param.implicit {
            self.output.write_char('}')?;
        }
        Ok(())
    }

    fn print_params(&mut self, params: &[Param], prefix: char) -> fmt::Result {
        if let Some((param, rest)) = params.split_first() {
            self.output.write_char(prefix)?;
            self.output.write_char(' ')?;
            self.print_param(param)?;
            self.output.write_str(". ")?;
            self.context.with_local(param, |rest_ctx| {
                let mut rest_printing_ctx = PrintingContext {
                    output: self.output,
                    context: rest_ctx,
                };
                rest_printing_ctx.print_params(rest, prefix)
            })?;
        }
        Ok(())
    }

    fn try_print_std_type_ctor(
        &mut self,
        expr: &Expr,
        kind: StandardTypeCtorKind,
        prefix: char,
        infix: char,
        parens_for_prefix: bool,
        parens_for_infix: bool,
    ) -> Result<bool, fmt::Error> {
        if let Some((domain, codomain)) = expr.match_indep_type(kind, self.context) {
            if parens_for_infix {
                self.output.write_char('(')?;
            }
            self.print_expr_with_parens(&domain, false, true, true, true, false)?;
            self.output.write_char(' ')?;
            self.output.write_char(infix)?;
            self.output.write_char(' ')?;
            self.print_expr_with_parens(
                &codomain,
                false,
                true,
                kind != StandardTypeCtorKind::Pi,
                true,
                false,
            )?;
            if parens_for_infix {
                self.output.write_char(')')?;
            }
            return Ok(true);
        }

        if let Some(lambda) = expr.match_dep_type_as_lambda(kind, false, self.context) {
            if parens_for_prefix {
                self.output.write_char('(')?;
            }
            self.output.write_char(prefix)?;
            self.output.write_char(' ')?;
            self.print_lambda(&lambda)?;
            if parens_for_prefix {
                self.output.write_char(')')?;
            }
            return Ok(true);
        }

        Ok(false)
    }

    fn try_print_eq_ctor(&mut self, expr: &Expr, parens: bool) -> Result<bool, fmt::Error> {
        if let Some((domain, left, right)) = expr.match_indep_eq_type(self.context) {
            if parens {
                self.output.write_char('(')?;
            }
            self.print_expr_with_parens(left, false, true, true, true, true)?;
            self.output.write_char(' ')?;
            self.output.write_char('=')?;
            let print_type = self.context.options().print_all_implicit_args;
            if print_type {
                self.output.write_char('{')?;
                self.print_expr(domain)?;
                self.output.write_char('}')?;
            }
            self.output.write_char(' ')?;
            self.print_expr_with_parens(right, false, true, true, true, true)?;
            if parens {
                self.output.write_char(')')?;
            }
            return Ok(true);
        }

        if let Some((left_domain, right_domain, domain_eq, left, right)) =
            expr.match_dep_eq_type(self.context)
        {
            if parens {
                self.output.write_char('(')?;
            }
            self.print_expr_with_parens(left, false, true, true, true, true)?;
            self.output.write_char(' ')?;
            self.output.write_char('=')?;
            let print_types = self.context.options().print_all_implicit_args;
            if print_types {
                self.output.write_char('{')?;
                self.print_expr(left_domain)?;
                self.output.write_char('}')?;
            }
            self.output.write_char('[')?;
            self.print_expr(domain_eq)?;
            self.output.write_char(']')?;
            if print_types {
                self.output.write_char('{')?;
                self.print_expr(right_domain)?;
                self.output.write_char('}')?;
            }
            self.output.write_char(' ')?;
            self.print_expr_with_parens(right, false, true, true, true, true)?;
            if parens {
                self.output.write_char(')')?;
            }
            return Ok(true);
        }

        Ok(false)
    }

    pub fn print_reduction_rule(&mut self, rule: &ReductionRule) -> fmt::Result {
        self.print_params(&rule.params, '∀')?;
        self.context.with_locals(&rule.params, |body_ctx| {
            let mut body_printing_ctx = PrintingContext {
                output: self.output,
                context: body_ctx,
            };
            body_printing_ctx.print_reduction_body(&rule.body)
        })
    }

    pub fn print_reduction_body(&mut self, body: &ReductionBody) -> fmt::Result {
        self.print_expr(&body.source)?;
        self.output.write_str(" :≡ ")?;
        self.print_expr(&body.target)
    }
}

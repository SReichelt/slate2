use std::fmt;

use super::{expr::*, metalogic::*};

use crate::generic::{context::*, expr_parts::*};

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
            DependentTypeCtorKind::Pi,
            'Π',
            '→',
            parens_for_lambda,
            parens_for_fun,
        )? {
            return Ok(());
        }

        if self.try_print_std_type_ctor(
            expr,
            DependentTypeCtorKind::Sigma,
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
                if let Expr::Lambda(lambda) = fun {
                    if parens_for_lambda {
                        self.output.write_char('(')?;
                    }
                    self.print_let_binding(lambda, arg)?;
                    if parens_for_lambda {
                        self.output.write_char(')')?;
                    }
                } else {
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
        }

        Ok(())
    }

    fn print_arg(&mut self, arg: &Arg, parens: bool) -> fmt::Result {
        if arg.implicit {
            self.output.write_char('{')?;
            self.print_expr(&arg.expr)?;
            self.output.write_char('}')?;
            Ok(())
        } else {
            self.print_expr_with_parens(&arg.expr, parens, parens, parens, parens, parens)
        }
    }

    fn print_lambda(&mut self, lambda: &LambdaExpr) -> fmt::Result {
        self.print_param(&lambda.param)?;
        self.output.write_str(". ")?;
        self.context.with_local(&lambda.param, |body_ctx| {
            let mut body_printing_ctx = PrintingContext {
                output: self.output,
                context: body_ctx,
            };
            body_printing_ctx.print_expr_with_parens(&lambda.body, false, false, false, true, false)
        })
    }

    fn print_let_binding(&mut self, lambda: &LambdaExpr, arg: &Arg) -> fmt::Result {
        self.output.write_char('[')?;
        self.print_param(&lambda.param)?;
        self.output.write_str(" ⫽ ")?;
        self.print_arg(arg, false)?;
        self.output.write_char(']')?;
        self.output.write_char(' ')?;
        self.context.with_local(&lambda.param, |body_ctx| {
            let mut body_printing_ctx = PrintingContext {
                output: self.output,
                context: body_ctx,
            };
            body_printing_ctx.print_expr(&lambda.body)
        })
    }

    fn print_param(&mut self, param: &Param) -> fmt::Result {
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
            self.context.with_local(&param, |rest_ctx| {
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
        kind: DependentTypeCtorKind,
        prefix: char,
        infix: char,
        parens_for_prefix: bool,
        parens_for_infix: bool,
    ) -> Result<bool, fmt::Error> {
        if let Some((domain, codomain)) = expr.match_generic_indep_type(kind, self.context) {
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
                kind != DependentTypeCtorKind::Pi,
                true,
                false,
            )?;
            if parens_for_infix {
                self.output.write_char(')')?;
            }
            return Ok(true);
        }

        if let Some(lambda) = expr.match_generic_dep_type(kind, false, self.context) {
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
        let ctx = self.context.as_minimal();
        let lambda_handler = self.context.lambda_handler();

        if let Ok((domain_param, left_param, right_param, generic_indep_eq_type)) =
            lambda_handler.get_generic_indep_eq_type(ctx)
        {
            if let Ok(Some(arg_vec)) = expr.match_expr(
                &ctx,
                &[domain_param, left_param, right_param],
                &generic_indep_eq_type,
            ) {
                if let [domain, left, right] = arg_vec.as_slice() {
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
            }
        }

        if let Ok((
            left_domain_param,
            right_domain_param,
            domain_eq_param,
            left_param,
            right_param,
            generic_dep_eq_type,
        )) = lambda_handler.get_generic_dep_eq_type(ctx)
        {
            if let Ok(Some(arg_vec)) = expr.match_expr(
                &ctx,
                &[
                    left_domain_param,
                    right_domain_param,
                    domain_eq_param,
                    left_param,
                    right_param,
                ],
                &generic_dep_eq_type,
            ) {
                if let [left_domain, right_domain, domain_eq, left, right] = arg_vec.as_slice() {
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
            }
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

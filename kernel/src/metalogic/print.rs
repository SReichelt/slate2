use std::fmt;

use super::{expr::*, metalogic::*};

use crate::generic::{context::*, expr::*};

pub struct PrintingContext<'a, 'b, W: fmt::Write> {
    pub output: &'a mut W,
    pub context: &'a MetaLogicContext<'b>,
}

impl<W: fmt::Write> PrintingContext<'_, '_, W> {
    pub fn print_expr(
        &mut self,
        expr: &Expr,
        parens_for_app: bool,
        parens_for_lambda: bool,
        parens_for_fun: bool,
        parens_for_prod: bool,
    ) -> fmt::Result {
        if self.try_print_special(
            expr,
            DependentTypeCtorKind::Pi,
            'Π',
            '→',
            parens_for_lambda,
            parens_for_fun,
        )? {
            return Ok(());
        }

        if self.try_print_special(
            expr,
            DependentTypeCtorKind::Sigma,
            'Σ',
            '×',
            parens_for_lambda,
            parens_for_prod,
        )? {
            return Ok(());
        }

        match expr {
            Expr::Var(Var(idx)) => {
                let param = self.context.get_var(*idx);
                param.print_name(self.output)?;
                let occurrence = self.context.get_name_occurrence(*idx, param);
                if occurrence != 0 {
                    self.output.write_fmt(format_args!("@{occurrence}"))?;
                }
            }
            Expr::App(app) => {
                if parens_for_app {
                    self.output.write_char('(')?;
                }
                self.print_expr(&app.param, false, true, true, true)?;
                self.output.write_char(' ')?;
                self.print_expr(&app.body, true, true, true, true)?;
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
        }
        Ok(())
    }

    fn print_lambda(&mut self, lambda: &LambdaExpr) -> fmt::Result {
        self.print_param(&lambda.param)?;
        self.output.write_str(". ")?;
        self.context.with_local(&lambda.param, |body_ctx| {
            let mut body_printing_ctx = PrintingContext {
                output: self.output,
                context: body_ctx,
            };
            body_printing_ctx.print_expr(&lambda.body, false, false, true, true)
        })?;
        Ok(())
    }

    fn print_param(&mut self, param: &Param) -> fmt::Result {
        param.print_name(self.output)?;
        self.output.write_str(" : ")?;
        self.print_expr(&param.type_expr, false, true, false, false)?;
        Ok(())
    }

    fn try_print_special(
        &mut self,
        expr: &Expr,
        kind: DependentTypeCtorKind,
        prefix: char,
        infix: char,
        parens_for_prefix: bool,
        parens_for_infix: bool,
    ) -> Result<bool, fmt::Error> {
        let ctx = self.context.as_minimal();
        let lambda_handler = self.context.lambda_handler();

        if let Ok((domain_param, codomain_param, generic_indep_type)) =
            lambda_handler.get_generic_indep_type(kind, ctx)
        {
            if let Some(arg_vec) =
                expr.match_expr(&[domain_param, codomain_param], &generic_indep_type, &ctx)
            {
                let domain = &arg_vec[0];
                let codomain = &arg_vec[1];
                if parens_for_infix {
                    self.output.write_char('(')?;
                }
                self.print_expr(&domain, false, true, true, true)?;
                self.output.write_char(' ')?;
                self.output.write_char(infix)?;
                self.output.write_char(' ')?;
                self.print_expr(
                    &codomain,
                    false,
                    true,
                    kind != DependentTypeCtorKind::Pi,
                    true,
                )?;
                if parens_for_infix {
                    self.output.write_char(')')?;
                }
                return Ok(true);
            }
        }

        if let Ok((domain_param, prop_param, generic_dep_type)) =
            lambda_handler.get_generic_dep_type(kind, ctx)
        {
            if let Some(arg_vec) =
                expr.match_expr(&[domain_param, prop_param], &generic_dep_type, &ctx)
            {
                if let Expr::Lambda(lambda) = &arg_vec[1] {
                    if parens_for_prefix {
                        self.output.write_char('(')?;
                    }
                    self.output.write_char(prefix)?;
                    self.output.write_char(' ')?;
                    self.print_lambda(lambda)?;
                    if parens_for_prefix {
                        self.output.write_char(')')?;
                    }
                    return Ok(true);
                }
            }
        }

        Ok(false)
    }
}

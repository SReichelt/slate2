use std::rc::Rc;

use smallvec::{smallvec, SmallVec};

use super::{expr::*, metalogic::*};

use crate::{
    generic::{context::*, context_object::*, expr_parts::*},
    util::parser::*,
};

pub struct ParsingContext<'a, 'b, 'c> {
    pub input: &'a mut ParserInput<'b>,
    pub context: &'a MetaLogicContext<'c>,
}

impl ParsingContext<'_, '_, '_> {
    pub fn parse_expr(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_prod()?;
        if self.input.try_read_char('→') {
            let codomain = self.parse_expr()?;
            expr = self.context.lambda_handler().get_indep_type(
                expr,
                codomain,
                DependentTypeCtorKind::Pi,
                self.context.as_minimal(),
            )?;
        }
        Ok(expr)
    }

    fn parse_prod(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_eq()?;
        if self.input.try_read_char('×') {
            let right = self.parse_eq()?;
            expr = self.context.lambda_handler().get_indep_type(
                expr,
                right,
                DependentTypeCtorKind::Sigma,
                self.context.as_minimal(),
            )?;
        }
        Ok(expr)
    }

    fn parse_eq(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_app()?;
        if self.input.try_read_char('=') {
            let mut domain = None;
            if self.input.try_read_char('{') {
                domain = Some(self.parse_expr()?);
                self.input.read_char('}')?;
            }
            if self.input.try_read_char('[') {
                let domain_eq = self.parse_expr()?;
                self.input.read_char(']')?;
                let mut right_domain = None;
                if self.input.try_read_char('{') {
                    right_domain = Some(self.parse_expr()?);
                    self.input.read_char('}')?;
                }
                let right = self.parse_app()?;
                if domain.is_none() {
                    if let Expr::Var(left_var) = &expr {
                        domain = Some(left_var.get_type(self.context));
                    } else {
                        let msg = format!("need to specify left type of dependent equality");
                        return self.input.error(msg);
                    }
                }
                if right_domain.is_none() {
                    if let Expr::Var(right_var) = &right {
                        right_domain = Some(right_var.get_type(self.context));
                    } else {
                        let msg = format!("need to specify right type of dependent equality");
                        return self.input.error(msg);
                    }
                }
                expr = self.context.lambda_handler().get_dep_eq_type(
                    domain.unwrap(),
                    right_domain.unwrap(),
                    domain_eq,
                    expr,
                    right,
                    self.context.as_minimal(),
                )?;
            } else {
                let right = self.parse_app()?;
                if domain.is_none() {
                    if let Expr::Var(left_var) = &expr {
                        domain = Some(left_var.get_type(self.context));
                    } else if let Expr::Var(right_var) = &right {
                        domain = Some(right_var.get_type(self.context));
                    } else {
                        let msg = format!("need to specify type of equality");
                        return self.input.error(msg);
                    }
                }
                expr = self.context.lambda_handler().get_indep_eq_type(
                    domain.unwrap(),
                    expr,
                    right,
                    self.context.as_minimal(),
                )?;
            }
        }
        Ok(expr)
    }

    fn parse_app(&mut self) -> Result<Expr, String> {
        self.input.skip_whitespace();
        if let Some(mut expr) = self.try_parse_one()? {
            self.input.skip_whitespace();
            while let Some(arg) = self.try_parse_one()? {
                expr = Expr::app(expr, arg);
                self.input.skip_whitespace();
            }
            Ok(expr)
        } else {
            self.input.expected("expression")
        }
    }

    fn try_parse_one(&mut self) -> Result<Option<Expr>, String> {
        if self.input.try_read_char('(') {
            let expr = self.parse_expr()?;
            self.input.read_char(')')?;
            Ok(Some(expr))
        } else if self.input.try_read_char('λ') {
            let (params, body) = self.parse_lambda()?;
            Ok(Some(Expr::multi_lambda(params, body)))
        } else if self.input.try_read_char('Π') {
            let expr = self.parse_dep_type(DependentTypeCtorKind::Pi)?;
            Ok(Some(expr))
        } else if self.input.try_read_char('Σ') {
            let expr = self.parse_dep_type(DependentTypeCtorKind::Sigma)?;
            Ok(Some(expr))
        } else if let Some((name, occurrence)) = self.input.try_read_name_with_occurrence() {
            if let Some(var_idx) = self.context.get_var_index(name, occurrence) {
                Ok(Some(Expr::var(var_idx)))
            } else {
                let msg = format!("variable '{name}' not found");
                self.input.error(msg)
            }
        } else {
            Ok(None)
        }
    }

    fn parse_lambda(&mut self) -> Result<(SmallVec<[Param; INLINE_PARAMS]>, Expr), String> {
        self.input.skip_whitespace();
        if let Some(param_name_str) = self.input.try_read_name() {
            let mut param_names: SmallVec<[String; INLINE_PARAMS]> =
                smallvec![param_name_str.into()];
            self.input.skip_whitespace();
            while let Some(param_name_str) = self.input.try_read_name() {
                param_names.push(param_name_str.into());
                self.input.skip_whitespace();
            }
            self.input.read_char(':')?;
            let param_type = self.parse_expr()?;
            self.input.read_char('.')?;
            let mut params: SmallVec<[Param; INLINE_PARAMS]> =
                SmallVec::with_capacity(param_names.len());
            let locals_start = self.context.locals_start();
            let mut shift: VarIndex = 0;
            for param_name in param_names {
                let name = if param_name == "_" {
                    None
                } else {
                    Some(Rc::new(param_name))
                };
                params.push(Param {
                    name,
                    type_expr: param_type.shifted_impl(locals_start, 0, shift),
                });
                shift -= 1;
            }
            let body = self.context.with_locals(&params, |body_ctx| {
                let mut body_parsing_ctx = ParsingContext {
                    input: self.input,
                    context: body_ctx,
                };
                body_parsing_ctx.parse_expr()
            })?;
            Ok((params, body))
        } else {
            self.input.expected("identifier")
        }
    }

    fn parse_dep_type(&mut self, kind: DependentTypeCtorKind) -> Result<Expr, String> {
        let (mut params, body) = self.parse_lambda()?;
        self.create_multi_dep_type(&mut params, body, kind, self.context.as_minimal())
    }

    fn create_multi_dep_type(
        &self,
        params: &mut [Param],
        body: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<Expr, String> {
        if let Some((param, rest_params)) = params.split_first_mut() {
            let rest = ctx.with_local(param, |rest_ctx| {
                self.create_multi_dep_type(rest_params, body, kind, *rest_ctx)
            })?;
            let domain = param.type_expr.clone();
            let prop = Expr::lambda(std::mem::take(param), rest);
            self.context
                .lambda_handler()
                .get_dep_type(domain, prop, kind, ctx)
        } else {
            Ok(body)
        }
    }
}

use std::rc::Rc;

use smallvec::{smallvec, SmallVec};

use super::{expr::*, metalogic::*};

use crate::{
    generic::{context_object::*, expr::*},
    util::parser::*,
};

pub struct ParsingContext<'a, 'b, 'c, 'd: 'c> {
    pub input: &'a mut ParserInput<'b>,
    pub context: &'a MetaLogicContext<'c, 'd, 'a>,
}

impl<'a, 'b, 'c, 'd> ParsingContext<'a, 'b, 'c, 'd> {
    pub fn parse_expr(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_prod()?;
        if self.input.try_read_char('→') {
            let codomain = self.parse_expr()?;
            expr = self.context.lambda_handler.get_indep_type(
                expr,
                codomain,
                DependentTypeCtorKind::Pi,
                self.context.context.locals_start(),
            )?;
        }
        Ok(expr)
    }

    fn parse_prod(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_app()?;
        if self.input.try_read_char('×') {
            let right = self.parse_app()?;
            expr = self.context.lambda_handler.get_indep_type(
                expr,
                right,
                DependentTypeCtorKind::Sigma,
                self.context.context.locals_start(),
            )?;
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
            if let Some(var_idx) = self.context.context.get_var_index(name, occurrence) {
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
            let locals_start = self.context.context.locals_start();
            let mut shift: VarIndex = 0;
            for param_name in param_names {
                let name = if param_name == "_" {
                    None
                } else {
                    Some(Rc::new(param_name))
                };
                params.push(Param {
                    name,
                    type_expr: param_type.with_shifted_vars(locals_start, 0, shift),
                });
                shift -= 1;
            }
            let mut body_ctx = ParsingContext {
                input: self.input,
                context: &self.context.with_locals(&params),
            };
            let body = body_ctx.parse_expr()?;
            Ok((params, body))
        } else {
            self.input.expected("identifier")
        }
    }

    fn parse_dep_type(&mut self, kind: DependentTypeCtorKind) -> Result<Expr, String> {
        let (mut params, body) = self.parse_lambda()?;
        self.create_multi_dep_type(&mut params, body, kind, self.context.context.locals_start())
    }

    fn create_multi_dep_type(
        &self,
        params: &mut [Param],
        body: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<Expr, String> {
        if let Some((param, rest_params)) = params.split_first_mut() {
            let rest = self.create_multi_dep_type(rest_params, body, kind, locals_start - 1)?;
            let domain = param.type_expr.clone();
            let prop = Expr::lambda(std::mem::take(param), rest);
            self.context
                .lambda_handler
                .get_dep_type(domain, prop, kind, locals_start)
        } else {
            Ok(body)
        }
    }
}

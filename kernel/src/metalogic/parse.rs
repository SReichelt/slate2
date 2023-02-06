use std::mem::take;

use anyhow::{anyhow, Result};
use smallvec::{smallvec, SmallVec};
use symbol_table::Symbol;

use super::{expr::*, metalogic::*};

use crate::{
    generic::{context::*, context_object::*, expr_parts::*},
    util::parser::*,
};

pub struct ParsingContext<'a, 'b, 'c> {
    input: &'a mut ParserInput<'b>,
    context: &'a MetaLogicContext<'c>,
}

impl ParsingContext<'_, '_, '_> {
    pub fn parse<R>(
        s: &str,
        ctx: &MetaLogicContext,
        f: impl FnOnce(&mut ParsingContext) -> Result<R>,
    ) -> Result<R> {
        let mut parser_input = ParserInput(s);
        let mut parsing_context = ParsingContext {
            input: &mut parser_input,
            context: ctx,
        };
        let result = f(&mut parsing_context)?;
        parser_input.expect_end()?;
        Ok(result)
    }

    pub fn parse_expr(&mut self) -> Result<Expr> {
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

    fn parse_prod(&mut self) -> Result<Expr> {
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

    fn parse_eq(&mut self) -> Result<Expr> {
        let mut expr = self.parse_app()?;
        if self.input.try_read_char('=') {
            let mut domain = Expr::Placeholder;
            if self.input.try_read_char('{') {
                domain = self.parse_expr()?;
                self.input.read_char('}')?;
            }
            if self.input.try_read_char('[') {
                let domain_eq = self.parse_expr()?;
                self.input.read_char(']')?;
                let mut right_domain = Expr::Placeholder;
                if self.input.try_read_char('{') {
                    right_domain = self.parse_expr()?;
                    self.input.read_char('}')?;
                }
                let right = self.parse_app()?;
                expr = self.context.lambda_handler().get_dep_eq_type(
                    domain,
                    right_domain,
                    domain_eq,
                    expr,
                    right,
                    self.context.as_minimal(),
                )?;
            } else {
                let right = self.parse_app()?;
                expr = self.context.lambda_handler().get_indep_eq_type(
                    domain,
                    expr,
                    right,
                    self.context.as_minimal(),
                )?;
            }
        }
        Ok(expr)
    }

    fn parse_app(&mut self) -> Result<Expr> {
        self.input.skip_whitespace();
        if let Some(mut expr) = self.try_parse_one()? {
            while let Some(arg) = self.try_parse_arg()? {
                expr = Expr::app(expr, arg);
                self.input.skip_whitespace();
            }
            Ok(expr)
        } else {
            self.input.expected("expression")
        }
    }

    fn try_parse_one(&mut self) -> Result<Option<Expr>> {
        if self.input.try_read_char('(') {
            let expr = self.parse_expr()?;
            self.input.read_char(')')?;
            Ok(Some(expr))
        } else if self.input.try_read_char('[') {
            let param = self.parse_param()?;
            self.input.read_char('⫽')?;
            let arg = self.parse_delimited_arg()?;
            self.input.read_char(']')?;
            let body = self.context.with_local(&param, |body_ctx| {
                let mut body_parsing_ctx = ParsingContext {
                    input: self.input,
                    context: body_ctx,
                };
                body_parsing_ctx.parse_expr()
            })?;
            Ok(Some(Expr::let_binding(param, arg, body)))
        } else if self.input.try_read_char('λ') {
            let (params, body) = self.parse_lambda()?;
            Ok(Some(Expr::multi_lambda(params, body)))
        } else if self.input.try_read_char('Π') {
            let expr = self.parse_dep_type(DependentTypeCtorKind::Pi)?;
            Ok(Some(expr))
        } else if self.input.try_read_char('Σ') {
            let expr = self.parse_dep_type(DependentTypeCtorKind::Sigma)?;
            Ok(Some(expr))
        } else if let Some(name) = self.input.try_read_name() {
            if name == "_" {
                Ok(Some(Expr::Placeholder))
            } else {
                let mut occurrence = 0;
                while self.input.try_read_char('⁺') {
                    occurrence += 1;
                }
                if let Some(var_idx) = self.context.get_named_var_index(name, occurrence) {
                    Ok(Some(Expr::var(var_idx)))
                } else {
                    let err = anyhow!("variable '{name}' not found");
                    self.input.error(err)
                }
            }
        } else {
            Ok(None)
        }
    }

    fn parse_delimited_arg(&mut self) -> Result<Arg> {
        self.input.skip_whitespace();
        if self.input.try_read_char('{') {
            let expr = self.parse_expr()?;
            self.input.read_char('}')?;
            Ok(Arg {
                expr,
                implicit: true,
            })
        } else {
            let expr = self.parse_expr()?;
            Ok(Arg {
                expr,
                implicit: false,
            })
        }
    }

    fn try_parse_arg(&mut self) -> Result<Option<Arg>> {
        self.input.skip_whitespace();
        if self.input.try_read_char('{') {
            let expr = self.parse_expr()?;
            self.input.read_char('}')?;
            Ok(Some(Arg {
                expr,
                implicit: true,
            }))
        } else if let Some(expr) = self.try_parse_one()? {
            Ok(Some(Arg {
                expr,
                implicit: false,
            }))
        } else {
            Ok(None)
        }
    }

    fn get_param_name(&mut self, param_name_str: &str) -> Option<Symbol> {
        if param_name_str == "_" {
            None
        } else {
            Some(self.context.intern_name(param_name_str))
        }
    }

    pub fn parse_param(&mut self) -> Result<Param> {
        self.input.skip_whitespace();
        let mut implicit = false;
        if self.input.try_read_char('{') {
            implicit = true;
        }
        if let Some(param_name_str) = self.input.try_read_name() {
            let param_name = self.get_param_name(param_name_str);
            self.input.skip_whitespace();
            let param_type = if self.input.try_read_char(':') {
                self.parse_expr()?
            } else {
                Expr::Placeholder
            };
            if implicit {
                self.input.read_char('}')?;
            }
            Ok(Param {
                name: param_name,
                type_expr: param_type,
                implicit,
            })
        } else {
            self.input.expected("identifier")
        }
    }

    fn parse_lambda(&mut self) -> Result<(SmallVec<[Param; INLINE_PARAMS]>, Expr)> {
        let params = self.parse_lambda_params()?;
        let body = self.context.with_locals(&params, |body_ctx| {
            let mut body_parsing_ctx = ParsingContext {
                input: self.input,
                context: body_ctx,
            };
            body_parsing_ctx.parse_expr()
        })?;
        Ok((params, body))
    }

    fn parse_lambda_params(&mut self) -> Result<SmallVec<[Param; INLINE_PARAMS]>> {
        self.input.skip_whitespace();
        let mut implicit = false;
        if self.input.try_read_char('{') {
            implicit = true;
        }
        if let Some(param_name_str) = self.input.try_read_name() {
            let mut param_names: SmallVec<[Option<Symbol>; INLINE_PARAMS]> =
                smallvec![self.get_param_name(param_name_str)];
            self.input.skip_whitespace();
            while let Some(param_name_str) = self.input.try_read_name() {
                param_names.push(self.get_param_name(param_name_str));
                self.input.skip_whitespace();
            }
            let param_type = if self.input.try_read_char(':') {
                self.parse_expr()?
            } else {
                Expr::Placeholder
            };
            if implicit {
                self.input.read_char('}')?;
            }
            self.input.read_char('.')?;
            let mut params: SmallVec<[Param; INLINE_PARAMS]> =
                SmallVec::with_capacity(param_names.len());
            let locals_start = self.context.locals_start();
            let mut shift: VarIndex = 0;
            for param_name in param_names {
                params.push(Param {
                    name: param_name,
                    type_expr: param_type.shifted_impl(locals_start, 0, shift),
                    implicit,
                });
                shift -= 1;
            }
            Ok(params)
        } else {
            self.input.expected("identifier")
        }
    }

    fn parse_dep_type(&mut self, kind: DependentTypeCtorKind) -> Result<Expr> {
        let (mut params, body) = self.parse_lambda()?;
        self.create_multi_dep_type(&mut params, body, kind, self.context.as_minimal())
    }

    fn create_multi_dep_type(
        &self,
        params: &mut [Param],
        body: Expr,
        kind: DependentTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<Expr> {
        if let Some((param, rest_params)) = params.split_first_mut() {
            let rest = ctx.with_local(param, |rest_ctx| {
                self.create_multi_dep_type(rest_params, body, kind, *rest_ctx)
            })?;
            let domain = param.type_expr.clone();
            let prop = Expr::lambda(take(param), rest);
            self.context
                .lambda_handler()
                .get_dep_type(domain, prop, kind, ctx)
        } else {
            Ok(body)
        }
    }

    pub fn parse_reduction_rule(&mut self, const_idx: VarIndex) -> Result<ReductionRule> {
        let mut params = SmallVec::new();
        self.input.skip_whitespace();
        while self.input.try_read_char('∀') {
            let mut new_params = self.context.with_locals(&params, |new_params_ctx| {
                let mut new_params_parsing_ctx = ParsingContext {
                    input: self.input,
                    context: new_params_ctx,
                };
                new_params_parsing_ctx.parse_lambda_params()
            })?;
            params.append(&mut new_params);
            self.input.skip_whitespace();
        }
        let body = self.context.with_locals(&params, |body_ctx| {
            let mut body_parsing_ctx = ParsingContext {
                input: self.input,
                context: body_ctx,
            };
            body_parsing_ctx.parse_reduction_body(const_idx)
        })?;
        Ok(ReductionRule { params, body })
    }

    pub fn parse_reduction_body(&mut self, const_idx: VarIndex) -> Result<ReductionBody> {
        let source = self.parse_expr()?;
        self.input.read_char_seq(":≡")?;
        let target = self.parse_expr()?;
        if let Some((source_const_idx, source_app_len)) = source.get_const_app_info() {
            if source_const_idx == const_idx {
                return Ok(ReductionBody {
                    source,
                    target,
                    source_app_len,
                });
            }
        }
        self.input.error(anyhow!(
            "source of reduction rule must be an application of the corresponding constant"
        ))
    }
}

use std::mem::take;

use anyhow::{anyhow, Result};
use smallvec::smallvec;
use symbol_table::Symbol;

use slate_kernel_generic::{context::*, context_object::*};
use slate_kernel_util::parser::*;

use crate::{expr::*, metalogic::*, metalogic_context::*};

pub struct ParsingContext<'a, 'b, 'c> {
    pub input: &'a mut StringInput<'b>,
    pub context: &'a MetaLogicContext<'c>,
}

impl ParsingContext<'_, '_, '_> {
    pub fn parse<R>(
        s: &str,
        ctx: &MetaLogicContext,
        f: impl FnOnce(&mut ParsingContext) -> Result<R>,
    ) -> Result<R> {
        let mut parser_input = StringInput(s);
        let mut parsing_context = ParsingContext {
            input: &mut parser_input,
            context: ctx,
        };
        let result = f(&mut parsing_context)?;
        parser_input.expect_end()?;
        Ok(result)
    }

    fn with_locals<R>(&mut self, params: &[Param], f: impl FnOnce(&mut ParsingContext) -> R) -> R {
        self.context.with_locals(params, |context| {
            let mut printing_context = ParsingContext {
                input: self.input,
                context,
            };
            f(&mut printing_context)
        })
    }

    pub fn parse_expr(&mut self) -> Result<Expr> {
        let mut expr = self.parse_prod()?;
        if self.input.try_read_char('→') {
            let codomain = self.parse_expr()?;
            expr =
                self.context
                    .config()
                    .get_indep_type(expr, codomain, StandardTypeCtorKind::Pi)?;
        }
        Ok(expr)
    }

    fn parse_prod(&mut self) -> Result<Expr> {
        let mut expr = self.parse_eq()?;
        if self.input.try_read_char('×') {
            let right = self.parse_eq()?;
            expr =
                self.context
                    .config()
                    .get_indep_type(expr, right, StandardTypeCtorKind::Sigma)?;
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
                expr = self.context.config().get_dep_eq_type(
                    domain,
                    right_domain,
                    domain_eq,
                    expr,
                    right,
                )?;
            } else {
                let right = self.parse_app()?;
                expr = self
                    .context
                    .config()
                    .get_indep_eq_type(domain, expr, right)?;
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
            let (params, args) = self.parse_let_binding()?;
            self.input.read_char(']')?;
            let body = self.with_locals(&params, |body_ctx| body_ctx.parse_expr())?;
            Ok(Some(Expr::dyn_let_binding(params, args, body)))
        } else if self.input.try_read_char('λ') {
            let (params, body) = self.parse_lambda()?;
            Ok(Some(Expr::dyn_multi_lambda(params, body)))
        } else if self.input.try_read_char('Π') {
            let expr = self.parse_dep_type(StandardTypeCtorKind::Pi)?;
            Ok(Some(expr))
        } else if self.input.try_read_char('Σ') {
            let expr = self.parse_dep_type(StandardTypeCtorKind::Sigma)?;
            Ok(Some(expr))
        } else if let Some(name) = self.input.try_read_ascii_identifier() {
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
            if self.input.try_read_char('{') {
                let expr = self.parse_expr()?;
                self.input.read_char('}')?;
                self.input.read_char('}')?;
                Ok(Arg {
                    expr,
                    implicit: true,
                    match_all: true,
                })
            } else {
                let expr = self.parse_expr()?;
                self.input.read_char('}')?;
                Ok(Arg {
                    expr,
                    implicit: true,
                    match_all: false,
                })
            }
        } else {
            let expr = self.parse_expr()?;
            Ok(Arg {
                expr,
                implicit: false,
                match_all: false,
            })
        }
    }

    fn try_parse_arg(&mut self) -> Result<Option<Arg>> {
        self.input.skip_whitespace();
        if self.input.try_read_char('{') {
            if self.input.try_read_char('{') {
                let expr = self.parse_expr()?;
                self.input.read_char('}')?;
                self.input.read_char('}')?;
                Ok(Some(Arg {
                    expr,
                    implicit: true,
                    match_all: true,
                }))
            } else {
                let expr = self.parse_expr()?;
                self.input.read_char('}')?;
                Ok(Some(Arg {
                    expr,
                    implicit: true,
                    match_all: false,
                }))
            }
        } else if let Some(expr) = self.try_parse_one()? {
            Ok(Some(Arg {
                expr,
                implicit: false,
                match_all: false,
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
        if let Some(param_name_str) = self.input.try_read_ascii_identifier() {
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

    fn parse_lambda(&mut self) -> Result<(InlineVec<Param>, Expr)> {
        let params = self.parse_lambda_params()?;
        let body = self.with_locals(&params, |body_ctx| body_ctx.parse_expr())?;
        Ok((params, body))
    }

    fn parse_lambda_params(&mut self) -> Result<InlineVec<Param>> {
        self.input.skip_whitespace();
        let mut implicit = false;
        if self.input.try_read_char('{') {
            implicit = true;
        }
        if let Some(param_name_str) = self.input.try_read_ascii_identifier() {
            let mut param_names: InlineVec<Option<Symbol>> =
                smallvec![self.get_param_name(param_name_str)];
            self.input.skip_whitespace();
            while let Some(param_name_str) = self.input.try_read_ascii_identifier() {
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
            let mut params: InlineVec<Param> = InlineVec::with_capacity(param_names.len());
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

    fn parse_dep_type(&mut self, kind: StandardTypeCtorKind) -> Result<Expr> {
        let (mut params, body) = self.parse_lambda()?;
        self.create_multi_dep_type(&mut params, body, kind, self.context.as_minimal())
    }

    fn create_multi_dep_type(
        &self,
        params: &mut [Param],
        body: Expr,
        kind: StandardTypeCtorKind,
        ctx: MinimalContext,
    ) -> Result<Expr> {
        if let Some((param, rest_params)) = params.split_first_mut() {
            let rest = ctx.with_local(param, |rest_ctx| {
                self.create_multi_dep_type(rest_params, body, kind, *rest_ctx)
            })?;
            let domain = param.type_expr.clone();
            let prop = Expr::lambda(take(param), rest);
            self.context.config().get_dep_type(domain, prop, kind)
        } else {
            Ok(body)
        }
    }

    pub fn parse_let_binding(&mut self) -> Result<(InlineVec<Param>, InlineVec<Arg>)> {
        let mut params = InlineVec::new();
        let mut args = InlineVec::new();
        loop {
            let new_param =
                self.with_locals(&params, |new_param_ctx| new_param_ctx.parse_param())?;
            params.push(new_param);
            self.input.read_char('⫽')?;
            args.push(self.parse_delimited_arg()?);
            self.input.skip_whitespace();
            if !self.input.try_read_char(';') {
                return Ok((params, args));
            }
        }
    }

    pub fn parse_named_reduction_rule(
        &mut self,
        const_idx: VarIndex,
    ) -> Result<(String, ReductionRule)> {
        if let Some(name) = self.input.try_read_ascii_identifier() {
            self.input.read_char(':')?;
            let rule = self.parse_reduction_rule(const_idx)?;
            Ok((name.to_owned(), rule))
        } else {
            self.input.expected("identifier")
        }
    }

    pub fn parse_reduction_rule(&mut self, const_idx: VarIndex) -> Result<ReductionRule> {
        let mut params = InlineVec::new();
        self.input.skip_whitespace();
        while self.input.try_read_char('∀') {
            let mut new_params = self.with_locals(&params, |new_params_ctx| {
                new_params_ctx.parse_lambda_params()
            })?;
            params.append(&mut new_params);
            self.input.skip_whitespace();
        }
        let body =
            self.with_locals(&params, |body_ctx| body_ctx.parse_reduction_body(const_idx))?;
        Ok(ReductionRule { params, body })
    }

    pub fn parse_reduction_body(&mut self, const_idx: VarIndex) -> Result<ReductionBody> {
        let source = self.parse_expr()?;
        self.input.read_char_seq(":≡")?;
        let target = self.parse_expr()?;
        if let Some((source_const_idx, source_app_len)) = source.get_const_app_info() {
            if source_const_idx == const_idx {
                return Ok(ReductionBody {
                    domain: Expr::Placeholder,
                    source,
                    target,
                    source_app_len,
                    eq: Expr::Placeholder,
                });
            }
        }
        self.input.error(anyhow!(
            "source of reduction rule must be an application of the corresponding constant"
        ))
    }
}

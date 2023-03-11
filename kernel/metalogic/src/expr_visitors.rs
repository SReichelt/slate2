use anyhow::{anyhow, Result};

use slate_kernel_generic::context::*;

use crate::{expr::*, metalogic::*, metalogic_context::*};

pub trait ExprVisitor {
    fn expr(&self, _expr: &Expr, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn param(&self, _param: &Param, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn params(&self, params: &[Param], ctx: &MetaLogicContext) -> Result<()> {
        for param_idx in 0..params.len() {
            let (prev, next) = params.split_at(param_idx);
            let param = &next[0];
            ctx.with_locals(prev, |param_ctx| self.param(param, param_ctx))?;
        }
        Ok(())
    }

    fn arg(&self, _arg: &Arg, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

pub struct DeepExprVisitor<Visitor: ExprVisitor>(pub Visitor);

impl<Visitor: ExprVisitor> ExprVisitor for DeepExprVisitor<Visitor> {
    fn expr(&self, expr: &Expr, ctx: &MetaLogicContext) -> Result<()> {
        match expr {
            Expr::Placeholder => {}
            Expr::Var(_) => {}
            Expr::App(app) => {
                self.arg(&app.param, ctx)?;
                self.expr(&app.body, ctx)?;
            }
            Expr::Lambda(lambda) => {
                self.param(&lambda.param, ctx)?;
                ctx.with_local(&lambda.param, |body_ctx| self.expr(&lambda.body, body_ctx))?;
            }
        }

        self.0.expr(expr, ctx)
    }

    fn param(&self, param: &Param, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&param.type_expr, ctx)?;

        self.0.param(param, ctx)
    }

    fn arg(&self, arg: &Arg, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&arg.expr, ctx)?;

        self.0.arg(arg, ctx)
    }
}

pub struct ParamTypeChecker;

impl ExprVisitor for ParamTypeChecker {
    fn param(&self, param: &Param, ctx: &MetaLogicContext) -> Result<()> {
        let mut type_type = param.type_expr.get_type(ctx)?;
        let mut cmp_type_type = ctx.config().universe_type.clone();
        if type_type.is_defeq(&mut cmp_type_type, ctx)? {
            Ok(())
        } else {
            let type_str = param.type_expr.print(ctx);
            let type_type_str = type_type.print(ctx);
            let cmp_type_type_str = cmp_type_type.print(ctx);
            Err(anyhow!("parameter type «{type_str} : {type_type_str}» must have type «{cmp_type_type_str}» instead"))
        }
    }
}

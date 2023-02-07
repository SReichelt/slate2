use anyhow::Result;

use slate_kernel_generic::context::*;

use crate::{expr::*, expr_manipulators::*, metalogic::*, metalogic_context::*};

pub trait MetaLogicManipulator: MetaLogicVisitorBase + ExprManipulator {
    fn reduction_rule(&self, _rule: &mut ReductionRule, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_body(&self, _body: &mut ReductionBody, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

impl MetaLogicManipulator for ImplicitArgInserter {
    fn reduction_rule(&self, rule: &mut ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        self.params(&mut rule.params, ctx)?;
        ctx.with_locals(&rule.params, |body| {
            self.reduction_body(&mut rule.body, body)
        })
    }

    fn reduction_body(&self, body: &mut ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        let source_type = self.insert_implicit_args_and_get_type(&mut body.source, ctx)?;
        let target_type = self.insert_implicit_args_and_get_type(&mut body.target, ctx)?;

        let (_, source_app_len) = body.source.get_app_info();
        body.source_app_len = source_app_len;

        Expr::check_type_arg_implicitness(&source_type, &target_type, ctx)
    }
}

impl MetaLogicManipulator for PlaceholderFiller {
    fn reduction_rule(&self, rule: &mut ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        self.params(&mut rule.params, ctx)?;
        ctx.with_locals(&rule.params, |body| {
            self.reduction_body(&mut rule.body, body)
        })
    }

    fn reduction_body(&self, body: &mut ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        let source_type = self.fill_placeholders(&mut body.source, Expr::Placeholder, ctx)?;
        self.fill_placeholders(&mut body.target, source_type, ctx)?;
        Ok(())
    }
}

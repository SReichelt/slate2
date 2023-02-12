use anyhow::{anyhow, Result};

use slate_kernel_generic::{context::*, context_object::ContextObject};

use crate::{expr::*, expr_manipulators::*, metalogic::*, metalogic_context::*};

impl MetaLogicVisitorBase for ImplicitArgInserter {
    fn get_constant_title(&self, name: &str) -> Option<String> {
        Some(format!(
            "insert implicit arguments in type of constant «{name}»"
        ))
    }

    fn get_rules_title(&self, name: &str) -> Option<String> {
        Some(format!(
            "insert implicit arguments in reduction rules of constant «{name}»"
        ))
    }

    fn get_constant_error_prefix(&self, name: &str, param_str: &str) -> String {
        format!("invalid implicit arguments in type of constant «{name}»\n(«{param_str}»)")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("invalid implicit arguments in reduction rule for «{name}»\n(«{rule_str}»)")
    }
}

impl MetaLogicVisitorBase for PlaceholderFiller {
    fn get_constant_title(&self, name: &str) -> Option<String> {
        Some(format!("fill placeholders in type of constant «{name}»"))
    }

    fn get_rules_title(&self, name: &str) -> Option<String> {
        Some(format!(
            "fill placeholders in reduction rules of constant «{name}»"
        ))
    }

    fn get_constant_error_prefix(&self, name: &str, param_str: &str) -> String {
        format!("unable to fill placeholder in type of constant «{name}»\n(«{param_str}»)")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("unable to fill placeholder in reduction rule for «{name}»\n(«{rule_str}»)")
    }
}

pub struct ReductionRuleArgReducer;

impl MetaLogicVisitorBase for ReductionRuleArgReducer {
    fn get_constant_title(&self, _: &str) -> Option<String> {
        None
    }

    fn get_rules_title(&self, name: &str) -> Option<String> {
        Some(format!(
            "reduce arguments of reduction rules of constant «{name}»"
        ))
    }

    fn get_constant_error_prefix(&self, name: &str, param_str: &str) -> String {
        format!("error reducing arguments in constant «{name}»\n(«{param_str}»)")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("error reducing arguments in reduction rule for «{name}»\n(«{rule_str}»)")
    }
}

pub trait MetaLogicManipulator: MetaLogicVisitorBase {
    fn constant(&self, _constant: &mut Constant, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_rule(&self, _rule: &mut ReductionRule, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_body(&self, _body: &mut ReductionBody, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

impl MetaLogicManipulator for ImplicitArgInserter {
    fn constant(&self, constant: &mut Constant, ctx: &MetaLogicContext) -> Result<()> {
        self.param(&mut constant.param, ctx)
    }

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
    fn constant(&self, constant: &mut Constant, ctx: &MetaLogicContext) -> Result<()> {
        self.param(&mut constant.param, ctx)
    }

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

impl MetaLogicManipulator for ReductionRuleArgReducer {
    fn reduction_rule(&self, rule: &mut ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        ctx.with_locals(&rule.params, |body| {
            self.reduction_body(&mut rule.body, body)
        })?;

        let mut idx = 0;
        for param in &rule.params {
            let next_idx = idx - 1;
            if !rule.body.source.has_refs_impl(next_idx, idx) {
                let name = ctx.get_display_name(param);
                return Err(anyhow!("match expression does not reference «{name}»"));
            }
            idx = next_idx;
        }

        Ok(())
    }

    fn reduction_body(&self, body: &mut ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        let mut fun = &mut body.source;
        while let Expr::App(app) = fun {
            app.param.expr.reduce(ctx, -1)?;
            fun = &mut app.body;
        }
        Ok(())
    }
}

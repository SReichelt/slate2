use anyhow::{anyhow, Result};

use slate_kernel_generic::{context::*, context_object::*};

use crate::{expr::*, expr_visitors::*, metalogic::*, metalogic_context::*};

impl<Visitor: MetaLogicVisitorBase + ExprVisitor> MetaLogicVisitorBase
    for DeepExprVisitor<Visitor>
{
    fn get_constant_title(&self, name: &str) -> Option<String> {
        self.0.get_constant_title(name)
    }

    fn get_rules_title(&self, name: &str) -> Option<String> {
        self.0.get_rules_title(name)
    }

    fn get_constant_error_prefix(&self, name: &str, param_str: &str) -> String {
        self.0.get_constant_error_prefix(name, param_str)
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        self.0.get_rule_error_prefix(name, rule_str)
    }
}

impl MetaLogicVisitorBase for ParamTypeChecker {
    fn get_constant_title(&self, name: &str) -> Option<String> {
        Some(format!("check types in type of constant «{name}»"))
    }

    fn get_rules_title(&self, name: &str) -> Option<String> {
        Some(format!(
            "check types in reduction rules of constant «{name}»"
        ))
    }

    fn get_constant_error_prefix(&self, name: &str, param_str: &str) -> String {
        format!("type of constant «{name}» is invalid\n(«{param_str}»)")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("types within reduction rule for «{name}» are invalid\n(«{rule_str}»)")
    }
}

pub struct ReductionRuleChecker;

impl MetaLogicVisitorBase for ReductionRuleChecker {
    fn get_constant_title(&self, _: &str) -> Option<String> {
        None
    }

    fn get_rules_title(&self, name: &str) -> Option<String> {
        Some(format!("check reduction rules of constant «{name}»"))
    }

    fn get_constant_error_prefix(&self, name: &str, param_str: &str) -> String {
        format!("error in constant «{name}» («{param_str}»)")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("error in reduction rule for «{name}» («{rule_str}»)")
    }
}

pub trait MetaLogicVisitor: MetaLogicVisitorBase {
    fn constant(&self, _constant: &Constant, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_rule(&self, _rule: &ReductionRule, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_body(&self, _body: &ReductionBody, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

impl<Visitor: MetaLogicVisitorBase + ExprVisitor> MetaLogicVisitor for DeepExprVisitor<Visitor> {
    fn constant(&self, constant: &Constant, ctx: &MetaLogicContext) -> Result<()> {
        self.param(&constant.param, ctx)
    }

    fn reduction_rule(&self, rule: &ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        self.params(&rule.params, ctx)?;
        ctx.with_locals(&rule.params, |body| self.reduction_body(&rule.body, body))
    }

    fn reduction_body(&self, body: &ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&body.source, ctx)?;
        self.expr(&body.target, ctx)
    }
}

impl MetaLogicVisitor for ReductionRuleChecker {
    fn reduction_rule(&self, rule: &ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        ctx.with_locals(&rule.params, |body| self.reduction_body(&rule.body, body))
    }

    fn reduction_body(&self, body: &ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        let source_type = body.source.get_type(ctx)?;
        let target_type = body.target.get_type(ctx)?;
        if source_type.compare(&target_type, ctx)? {
            Ok(())
        } else {
            let source_str = body.source.print(ctx);
            let source_type_str = source_type.print(ctx);
            let target_str = body.target.print(ctx);
            let target_type_str = target_type.print(ctx);
            Err(anyhow!("type conflict between «{source_str} : {source_type_str}»\nand «{target_str} : {target_type_str}»"))
        }
    }
}

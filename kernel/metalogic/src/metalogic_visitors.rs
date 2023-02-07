use anyhow::Result;

use slate_kernel_generic::context::*;

use crate::{expr_manipulators::*, expr_visitors::*, metalogic::*, metalogic_context::*};

impl<Visitor: MetaLogicVisitorBase + ExprVisitor> MetaLogicVisitorBase
    for DeepExprVisitor<Visitor>
{
    fn get_constant_error_prefix(&self, name: &str) -> String {
        self.0.get_constant_error_prefix(name)
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        self.0.get_rule_error_prefix(name, rule_str)
    }
}

impl MetaLogicVisitorBase for ParamTypeChecker {
    fn get_constant_error_prefix(&self, name: &str) -> String {
        format!("type of constant «{name}» is invalid")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("types within reduction rule for «{name}» are invalid («{rule_str}»)")
    }
}

impl MetaLogicVisitorBase for ImplicitArgInserter {
    fn get_constant_error_prefix(&self, name: &str) -> String {
        format!("invalid implicit arguments in type of constant «{name}»")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("invalid implicit arguments in reduction rule for «{name}» («{rule_str}»)")
    }
}

impl MetaLogicVisitorBase for PlaceholderFiller {
    fn get_constant_error_prefix(&self, name: &str) -> String {
        format!("unable to fill placeholder in type of constant «{name}»")
    }

    fn get_rule_error_prefix(&self, name: &str, rule_str: &str) -> String {
        format!("unable to fill placeholder in reduction rule for «{name}» («{rule_str}»)")
    }
}

pub trait MetaLogicVisitor: MetaLogicVisitorBase + ExprVisitor {
    fn reduction_rule(&self, _rule: &ReductionRule, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn reduction_body(&self, _body: &ReductionBody, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

impl<Visitor: MetaLogicVisitorBase + ExprVisitor> MetaLogicVisitor for DeepExprVisitor<Visitor> {
    fn reduction_rule(&self, rule: &ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        self.params(&rule.params, ctx)?;
        ctx.with_locals(&rule.params, |body| self.reduction_body(&rule.body, body))
    }

    fn reduction_body(&self, body: &ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&body.source, ctx)?;
        self.expr(&body.target, ctx)
    }
}

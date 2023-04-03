use std::sync::atomic::{AtomicBool, Ordering};

use anyhow::{anyhow, Result};

use slate_kernel_generic::{context::*, expr_parts::*};

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

    fn reduction_rule(&self, rule: &mut ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        ctx.with_locals(&rule.params, |body| {
            self.reduction_body(&mut rule.body, body)
        })
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
        let source_manipulator = PlaceholderFiller {
            force: false,
            match_var_ctx: Some(ctx.as_minimal()),
            has_unfilled_placeholders: AtomicBool::new(false),
            ..*self
        };
        let mut source_type =
            source_manipulator.fill_placeholders(&mut body.source, Expr::Placeholder, ctx)?;
        if source_manipulator
            .has_unfilled_placeholders
            .load(Ordering::Relaxed)
        {
            source_type =
                self.fill_placeholders(&mut body.source.clone(), Expr::Placeholder, ctx)?;
        }
        self.expr(&mut body.target, source_type, ctx)
    }
}

impl ReductionRuleArgReducer {
    fn has_matchable_ref(expr: &Expr, var_idx: VarIndex) -> bool {
        match expr {
            Expr::Var(Var(idx)) => *idx == var_idx,
            Expr::App(app) => {
                Self::has_matchable_ref(&app.body, var_idx)
                    || (!app.param.match_all && Self::has_matchable_ref(&app.param.expr, var_idx))
            }
            Expr::Lambda(lambda) => {
                Self::has_matchable_ref(&lambda.param.type_expr, var_idx)
                    || Self::has_matchable_ref(&lambda.body, var_idx - 1)
            }
            _ => false,
        }
    }
}

impl MetaLogicManipulator for ReductionRuleArgReducer {
    fn reduction_rule(&self, rule: &mut ReductionRule, ctx: &MetaLogicContext) -> Result<()> {
        ctx.with_locals(&rule.params, |body| {
            self.reduction_body(&mut rule.body, body)
        })?;

        let mut idx = -(rule.params.len() as VarIndex);
        for param in &rule.params {
            if !Self::has_matchable_ref(&rule.body.source, idx) {
                let name = ctx.get_display_name(param);
                return Err(anyhow!(
                    "match expression does not reference «{name}» in a suitable way"
                ));
            }
            idx += 1;
        }

        Ok(())
    }

    fn reduction_body(&self, body: &mut ReductionBody, ctx: &MetaLogicContext) -> Result<()> {
        let mut fun = &mut body.source;
        while let Expr::App(app) = fun {
            app.param.expr.reduce_all(ctx)?;
            fun = &mut app.body;
        }
        Ok(())
    }
}

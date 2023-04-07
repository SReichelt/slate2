use std::{
    fmt::{self, Debug},
    mem::take,
};

use anyhow::{anyhow, Result};
use smallvec::{smallvec, SmallVec};
use symbol_table::Symbol;

use slate_kernel_generic::{context::*, context_object::*, expr_parts::*};

use crate::{metalogic::*, metalogic_context::*, parse::*, print::*};

#[derive(Clone, PartialEq)]
pub enum Expr {
    Placeholder,
    Var(Var), // includes primitive constants
    App(Box<AppExpr>),
    Lambda(Box<LambdaExpr>),
    Cast(Box<CastExpr>),
}

impl Expr {
    pub fn var(idx: VarIndex) -> Self {
        Expr::Var(Var(idx))
    }

    pub fn app(fun: Expr, arg: Arg) -> Self {
        Expr::App(Box::new(App {
            param: arg,
            body: fun,
        }))
    }

    pub fn multi_app<const LEN: usize>(mut fun: Expr, args: [Arg; LEN]) -> Self {
        for arg in args {
            fun = Self::app(fun, arg);
        }
        fun
    }

    pub fn dyn_multi_app<const LEN: usize>(mut fun: Expr, args: SmallVec<[Arg; LEN]>) -> Self {
        for arg in args {
            fun = Self::app(fun, arg);
        }
        fun
    }

    pub fn apply(self, arg: Arg, ctx: &impl Context) -> Self {
        if let Expr::Lambda(lambda) = self {
            lambda.apply(arg, ctx)
        } else {
            Self::app(self, arg)
        }
    }

    pub fn lambda(param: Param, body: Expr) -> Self {
        Expr::Lambda(Box::new(Lambda { param, body }))
    }

    pub fn multi_lambda<const LEN: usize>(params: [Param; LEN], mut body: Expr) -> Self {
        for param in params.into_iter().rev() {
            body = Self::lambda(param, body);
        }
        body
    }

    pub fn dyn_multi_lambda<const LEN: usize>(
        params: SmallVec<[Param; LEN]>,
        mut body: Expr,
    ) -> Self {
        for param in params.into_iter().rev() {
            body = Self::lambda(param, body);
        }
        body
    }

    pub fn const_lambda(domain: Expr, mut body: Expr, ctx: &impl ParamContext<Param>) -> Self {
        let param = Param {
            name: None,
            type_expr: domain,
            implicit: false,
        };
        ctx.with_local(&param, |body_ctx| body.shift_to_subcontext(ctx, body_ctx));
        Self::lambda(param, body)
    }

    pub fn let_binding<const LEN: usize>(
        params: [Param; LEN],
        args: [Arg; LEN],
        body: Expr,
    ) -> Self {
        Expr::multi_app(Expr::multi_lambda(params, body), args)
    }

    pub fn dyn_let_binding<const LEN: usize>(
        params: SmallVec<[Param; LEN]>,
        args: SmallVec<[Arg; LEN]>,
        body: Expr,
    ) -> Self {
        Expr::dyn_multi_app(Expr::dyn_multi_lambda(params, body), args)
    }

    pub fn is_small(&self) -> bool {
        match self {
            Expr::Placeholder => true,
            Expr::Var(_) => true,
            Expr::App(_) => false,
            Expr::Lambda(_) => false,
            Expr::Cast(cast) => cast.expr.is_small(),
        }
    }

    pub fn reduce_all(&mut self, ctx: &MetaLogicContext) -> Result<ReductionTrace> {
        self.reduce(ctx, false, -1)
    }

    pub fn reduce(
        &mut self,
        ctx: &MetaLogicContext,
        head_only: bool,
        mut max_depth: i32,
    ) -> Result<ReductionTrace> {
        if self.is_empty() {
            return Ok(Vec::new());
        }

        if max_depth >= 0 {
            if max_depth == 0 {
                return Ok(Vec::new());
            }
            max_depth -= 1;
        }

        let apply_reduction_rules = ctx.options().reduce_with_reduction_rules;

        let mut reductions = Vec::new();

        loop {
            self.reduce_step_impl(ctx, head_only, max_depth, &mut reductions)?;

            if apply_reduction_rules {
                if let Some(applied_rule) = self.apply_reduction_rule(ctx)? {
                    if applied_rule {
                        reductions.push(ReductionStep::ReductionRuleApplication);
                        continue;
                    }
                } else if head_only {
                    // Indeterminate result with not-fully-reduced arguments: reduce them and retry.
                    let old_reductions_len = reductions.len();
                    self.reduce_step_impl(ctx, false, max_depth, &mut reductions)?;
                    if reductions.len() != old_reductions_len {
                        if let Some(true) = self.apply_reduction_rule(ctx)? {
                            reductions.push(ReductionStep::ReductionRuleApplication);
                            continue;
                        }
                    }
                }
            }

            break;
        }

        Ok(reductions)
    }

    fn reduce_step_impl(
        &mut self,
        ctx: &MetaLogicContext,
        head_only: bool,
        max_depth: i32,
        reductions: &mut ReductionTrace,
    ) -> Result<()> {
        loop {
            match self {
                Expr::Placeholder => {}
                Expr::Var(_) => {}
                Expr::App(app) => {
                    // Usually, we reduce inner expressions first. Note that this may enable beta
                    // reduction in the first place, so we would need to repeat it afterwards
                    // anyway.
                    // However, as an exception for better performance, we skip reduction of the
                    // argument if it is dropped.
                    if let Some(beta_reduced) = app.beta_reduce_if_trivial(ctx) {
                        *self = beta_reduced;
                        reductions.push(ReductionStep::BetaReduction);
                        continue;
                    }

                    let fun_reductions = app.body.reduce(ctx, head_only, max_depth)?;
                    if !fun_reductions.is_empty() {
                        reductions.push(ReductionStep::AppFunReduction(fun_reductions));
                    }

                    if !head_only {
                        // Reduction of function may have made beta reduction possible.
                        if let Some(beta_reduced) = app.beta_reduce_if_trivial(ctx) {
                            *self = beta_reduced;
                            reductions.push(ReductionStep::BetaReduction);
                            continue;
                        }

                        let arg_reductions = app.param.expr.reduce(ctx, head_only, max_depth)?;
                        if !arg_reductions.is_empty() {
                            reductions.push(ReductionStep::AppArgReduction(arg_reductions));
                        }
                    }

                    // Now always beta-reduce if possible.
                    if let Some(beta_reduced) = app.beta_reduce(ctx) {
                        *self = beta_reduced;
                        reductions.push(ReductionStep::BetaReduction);
                        continue;
                    }
                }
                Expr::Lambda(lambda) => {
                    if !head_only {
                        let param_type_reductions =
                            lambda.param.type_expr.reduce(ctx, head_only, max_depth)?;
                        if !param_type_reductions.is_empty() {
                            reductions.push(ReductionStep::LambdaParamTypeReduction(
                                param_type_reductions,
                            ));
                        }

                        if let Some(eta_reduced) =
                            ctx.with_local(&lambda.param, |body_ctx| -> Result<Option<Expr>> {
                                let body_reductions =
                                    lambda.body.reduce(body_ctx, head_only, max_depth)?;
                                if !body_reductions.is_empty() {
                                    reductions
                                        .push(ReductionStep::LambdaBodyReduction(body_reductions));
                                }

                                // Eta-reduction isn't really important, but it makes printed
                                // expressions easier to read.
                                if let Expr::App(app) = &mut lambda.body {
                                    if let Some(eta_reduced) = app.eta_reduce(ctx, body_ctx) {
                                        return Ok(Some(eta_reduced));
                                    }
                                }

                                Ok(None)
                            })?
                        {
                            *self = eta_reduced;
                            reductions.push(ReductionStep::EtaReduction);
                            continue;
                        }
                    }
                }
                Expr::Cast(cast) => {
                    let cast_expr_reductions = cast.expr.reduce(ctx, head_only, max_depth)?;
                    if !cast_expr_reductions.is_empty() {
                        reductions.push(ReductionStep::CastExprReduction(cast_expr_reductions));
                    }
                }
            }

            break;
        }

        Ok(())
    }

    fn apply_reduction_rule(&mut self, ctx: &MetaLogicContext) -> Result<Option<bool>> {
        let mut result = Some(false);

        if let Some((const_idx, app_len)) = self.get_const_app_info() {
            let constant = &ctx.constants()[const_idx as usize];
            for rule in &constant.reduction_rules {
                if rule.body.source_app_len == app_len {
                    if app_len == 0 && rule.params.is_empty() {
                        // Fast path for definitions without actual matching.
                        *self = rule.body.target.clone();
                        return Ok(Some(true));
                    } else if let Some(mut args) =
                        self.match_expr(ctx, &rule.params, &rule.body.source)?
                    {
                        let mut expr = rule.body.target.clone();
                        expr.substitute(&mut args, true, ctx);
                        *self = expr;
                        return Ok(Some(true));
                    } else {
                        // Indeterminate result: matching could succeed if arguments are reduced.
                        result = None;
                    }
                }
            }
        }

        Ok(result)
    }

    pub fn apply_one_reduction_rule(&mut self, ctx: &MetaLogicContext) -> Result<bool> {
        if let Some(true) = self.apply_reduction_rule(ctx)? {
            Ok(true)
        } else if let Expr::App(app) = self {
            if app.body.apply_one_reduction_rule(ctx)? {
                if let Some(beta_reduced) = app.beta_reduce(ctx) {
                    *self = beta_reduced;
                }
                Ok(true)
            } else {
                Ok(false)
            }
        } else {
            Ok(false)
        }
    }

    pub fn get_app_info(&self) -> (&Expr, usize) {
        let mut fun = self;
        let mut len = 0;
        while let Expr::App(app) = fun {
            len += 1;
            fun = &app.body;
        }
        (fun, len)
    }

    pub fn get_const_app_info(&self) -> Option<(VarIndex, usize)> {
        let (fun, len) = self.get_app_info();
        if let Expr::Var(Var(var_idx)) = fun {
            if *var_idx >= 0 {
                return Some((*var_idx, len));
            }
        }
        None
    }

    pub fn is_defeq(
        &mut self,
        expr: &mut Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Option<DefinitionalEquality>> {
        if self.compare(expr, ctx)? {
            return Ok(Some(DefinitionalEquality::trivial()));
        }

        // We could first reduce just enough to be sure that the two expressions cannot possibly be
        // definitionally equal, but `is_defeq` is really only meant to be called for verification,
        // not for matching.
        let self_reductions = self.reduce_all(ctx)?;
        let expr_reductions = expr.reduce_all(ctx)?;

        if !self_reductions.is_empty() || !expr_reductions.is_empty() && self.compare(expr, ctx)? {
            // TODO: optimize
            return Ok(Some(DefinitionalEquality {
                left: self_reductions,
                right: expr_reductions,
            }));
        }

        Ok(None)
    }

    pub fn convert_to_combinators(
        &mut self,
        ctx: &MetaLogicContext,
        mut max_depth: i32,
    ) -> Result<()> {
        if max_depth == 0 {
            return Ok(());
        }
        max_depth -= 1;

        loop {
            match self {
                Expr::Placeholder => {}
                Expr::Var(_) => {}
                Expr::App(app) => {
                    app.param.expr.convert_to_combinators(ctx, max_depth)?;
                    app.body.convert_to_combinators(ctx, max_depth)?;
                }
                Expr::Lambda(lambda) => {
                    lambda
                        .param
                        .type_expr
                        .convert_to_combinators(ctx, max_depth)?;
                    ctx.with_local(&lambda.param, |body_ctx| {
                        lambda.body.convert_to_combinators(body_ctx, max_depth)
                    })?;

                    *self = lambda.convert_to_combinator(ctx)?;
                    continue;
                }
                Expr::Cast(cast) => {
                    cast.expr.convert_to_combinators(ctx, max_depth)?;
                }
            }

            return Ok(());
        }
    }

    pub fn match_expr<Ctx: ComparisonContext>(
        &self,
        ctx: &Ctx,
        match_params: &[Param],
        match_expr: &Expr,
    ) -> Result<Option<SmallVec<[Expr; INLINE_PARAMS]>>> {
        if *self != Expr::Placeholder {
            let mut args: SmallVec<[Expr; INLINE_PARAMS]> =
                smallvec![Expr::default(); match_params.len()];
            if ctx.with_locals(match_params, |ctx_with_params| {
                match_expr.substitute_and_compare(ctx_with_params, &mut args, self, ctx)
            })? {
                return Ok(Some(args));
            }
        }
        Ok(None)
    }

    pub fn match_app<const LEN: usize>(&self, match_fun: &Expr) -> Option<[&Expr; LEN]> {
        let mut result = [self; LEN];
        let mut expr = self;
        for i in (0..LEN).rev() {
            if let Expr::App(app) = expr {
                expr = &app.body;
                result[i] = &app.param.expr;
            } else {
                return None;
            }
        }
        if expr == match_fun {
            Some(result)
        } else {
            None
        }
    }

    pub fn get_fun_type(
        param: &Param,
        mut body_type: Expr,
        ctx: &MetaLogicContext,
        body_ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        if !param.implicit && !body_type.is_empty() && body_type.valid_in_superctx(body_ctx, ctx) {
            body_type.shift_to_supercontext(body_ctx, ctx);
            ctx.config().get_indep_type(
                param.type_expr.clone(),
                body_type,
                StandardTypeCtorKind::Pi,
            )
        } else {
            let prop = Expr::lambda(param.clone(), body_type);
            ctx.config()
                .get_dep_type(param.type_expr.clone(), prop, StandardTypeCtorKind::Pi)
        }
    }

    pub fn match_indep_type(
        &self,
        kind: StandardTypeCtorKind,
        ctx: &MetaLogicContext,
    ) -> Option<(&Expr, &Expr)> {
        if *self != Expr::Placeholder {
            let ctor = ctx.config().get_indep_ctor(kind);
            if let Some([domain, codomain]) = self.match_app(ctor) {
                return Some((domain, codomain));
            }
        }
        None
    }

    pub fn match_dep_type(
        &self,
        kind: StandardTypeCtorKind,
        ctx: &MetaLogicContext,
    ) -> Option<(&Expr, &Expr)> {
        if *self != Expr::Placeholder {
            let ctor = ctx.config().get_dep_ctor(kind);
            if let Some([domain, prop]) = self.match_app(ctor) {
                return Some((domain, prop));
            }
        }
        None
    }

    pub fn match_dep_type_as_lambda(
        &self,
        kind: StandardTypeCtorKind,
        convert_to_lambda: bool,
        ctx: &MetaLogicContext,
    ) -> Option<LambdaExpr> {
        if let Some((domain, prop)) = self.match_dep_type(kind, ctx) {
            if let Expr::Lambda(lambda) = prop {
                return Some((**lambda).clone());
            } else if convert_to_lambda {
                let mut prop = prop.clone();
                let param = Param {
                    name: None,
                    type_expr: domain.clone(),
                    implicit: false,
                };
                ctx.with_local(&param, |subctx| {
                    prop.shift_to_subcontext(ctx, subctx);
                });
                return Some(Lambda {
                    param,
                    body: Expr::app(prop, Arg::explicit(Expr::var(-1))),
                });
            }
        }
        None
    }

    pub fn match_type_as_lambda(
        &self,
        kind: StandardTypeCtorKind,
        ctx: &MetaLogicContext,
    ) -> Option<LambdaExpr> {
        if let Some((domain, codomain)) = self.match_indep_type(kind, ctx) {
            let mut codomain = codomain.clone();
            let param = Param {
                name: None,
                type_expr: domain.clone(),
                implicit: false,
            };
            ctx.with_local(&param, |subctx| {
                codomain.shift_to_subcontext(ctx, subctx);
            });
            return Some(Lambda {
                param,
                body: codomain,
            });
        }

        self.match_dep_type_as_lambda(kind, true, ctx)
    }

    pub fn match_indep_eq_type(&self, ctx: &MetaLogicContext) -> Option<(&Expr, &Expr, &Expr)> {
        if *self != Expr::Placeholder {
            let ctor = &ctx.config().eq_ctor;
            if let Some([domain, left, right]) = self.match_app(ctor) {
                return Some((domain, left, right));
            }
        }
        None
    }

    pub fn match_dep_eq_type(
        &self,
        ctx: &MetaLogicContext,
    ) -> Option<(&Expr, &Expr, &Expr, &Expr, &Expr)> {
        if *self != Expr::Placeholder {
            let ctor = &ctx.config().eqd_ctor;
            if let Some([left_domain, right_domain, domain_eq, left, right]) = self.match_app(ctor)
            {
                return Some((left_domain, right_domain, domain_eq, left, right));
            }
        }
        None
    }

    pub fn check_type_arg_implicitness(
        type_1: &Self,
        type_2: &Self,
        ctx: &MetaLogicContext,
    ) -> Result<()> {
        if *type_1 != Expr::Placeholder && *type_2 != Expr::Placeholder {
            if let (Some(lambda_1), Some(lambda_2)) = (
                type_1.match_type_as_lambda(StandardTypeCtorKind::Pi, ctx),
                type_2.match_type_as_lambda(StandardTypeCtorKind::Pi, ctx),
            ) {
                if lambda_1.param.implicit != lambda_2.param.implicit {
                    let name_1 = ctx.get_display_name(&lambda_1.param);
                    let name_2 = ctx.get_display_name(&lambda_2.param);
                    return Err(anyhow!(
                        "implicitness of «{name_1}» does not match implicitness of «{name_2}»"
                    ));
                }

                return ctx.with_local(&lambda_1.param, |body_ctx| {
                    Self::check_type_arg_implicitness(&lambda_1.body, &lambda_2.body, body_ctx)
                });
            }
        }

        Ok(())
    }
}

impl Default for Expr {
    fn default() -> Self {
        Expr::Placeholder
    }
}

impl CanBeEmpty for Expr {
    fn is_empty(&self) -> bool {
        *self == Expr::Placeholder
    }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Placeholder => f.write_str("_"),
            Self::Var(var) => var.fmt(f),
            Self::App(app) => app.fmt(f),
            Self::Lambda(lambda) => lambda.fmt(f),
            Self::Cast(cast) => cast.fmt(f),
        }
    }
}

impl ContextObject for Expr {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        match self {
            Expr::Placeholder => {}
            Expr::Var(var) => var.shift_impl(start, end, shift),
            Expr::App(app) => app.shift_impl(start, end, shift),
            Expr::Lambda(lambda) => lambda.shift_impl(start, end, shift),
            Expr::Cast(cast) => cast.shift_impl(start, end, shift),
        }
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        match self {
            Expr::Placeholder => Expr::Placeholder,
            Expr::Var(var) => Expr::Var(var.shifted_impl(start, end, shift)),
            Expr::App(app) => Expr::App(Box::new(app.shifted_impl(start, end, shift))),
            Expr::Lambda(lambda) => Expr::Lambda(Box::new(lambda.shifted_impl(start, end, shift))),
            Expr::Cast(cast) => Expr::Cast(Box::new(cast.shifted_impl(start, end, shift))),
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        match self {
            Expr::Placeholder => {}
            Expr::Var(var) => var.count_refs_impl(start, ref_counts),
            Expr::App(app) => app.count_refs_impl(start, ref_counts),
            Expr::Lambda(lambda) => lambda.count_refs_impl(start, ref_counts),
            Expr::Cast(cast) => cast.count_refs_impl(start, ref_counts),
        }
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        match self {
            Expr::Placeholder => false,
            Expr::Var(var) => var.has_refs_impl(start, end),
            Expr::App(app) => app.has_refs_impl(start, end),
            Expr::Lambda(lambda) => lambda.has_refs_impl(start, end),
            Expr::Cast(cast) => cast.has_refs_impl(start, end),
        }
    }
}

impl ContextObjectWithSubst<Expr> for Expr {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [Expr],
        ref_counts: &mut [usize],
    ) {
        match self {
            Expr::Placeholder => {}
            Expr::Var(var) => {
                if let Some(subst_arg) =
                    var.get_subst_arg_impl(shift_start, args_start, args, ref_counts)
                {
                    *self = subst_arg;
                } else {
                    var.shift_impl(shift_start, args_start, args.len() as VarIndex);
                }
            }
            Expr::App(app) => app.substitute_impl(shift_start, args_start, args, ref_counts),
            Expr::Lambda(lambda) => {
                lambda.substitute_impl(shift_start, args_start, args, ref_counts)
            }
            Expr::Cast(cast) => cast.substitute_impl(shift_start, args_start, args, ref_counts),
        }
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithCmp<Ctx> for Expr {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        match (self, target) {
            (Expr::Placeholder, _) => Ok(true),
            (_, Expr::Placeholder) => Ok(true),
            (Expr::Var(var), Expr::Var(target_var)) => {
                var.shift_and_compare_impl(ctx, orig_ctx, target_var, target_subctx)
            }
            (Expr::App(app), Expr::App(target_app)) => {
                app.shift_and_compare_impl(ctx, orig_ctx, target_app, target_subctx)
            }
            (Expr::Lambda(lambda), Expr::Lambda(target_lambda)) => {
                lambda.shift_and_compare_impl(ctx, orig_ctx, target_lambda, target_subctx)
            }
            (Expr::Lambda(lambda), _) => {
                if let Some(cmb) = lambda.try_convert_to_combinator(ctx)? {
                    cmb.shift_and_compare_impl(ctx, orig_ctx, target, target_subctx)
                } else {
                    Ok(false)
                }
            }
            (Expr::Cast(cast), Expr::Cast(target_cast)) => {
                cast.shift_and_compare_impl(ctx, orig_ctx, target_cast, target_subctx)
            }
            (_, Expr::Lambda(target_lambda)) => {
                if let Some(target_cmb) = target_lambda.try_convert_to_combinator(ctx)? {
                    self.shift_and_compare_impl(ctx, orig_ctx, &target_cmb, target_subctx)
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        }
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithSubstCmp<Expr, Ctx> for Expr {
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [Expr],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if let Expr::Var(var) = self {
            if let Some(result) =
                var.compare_subst_arg_impl(ctx, args, subst_ctx, target, target_subctx)
            {
                return result;
            }
        }

        match (self, target) {
            (Expr::Placeholder, _) => Ok(true),
            (_, Expr::Placeholder) => Ok(true),
            (Expr::Var(var), Expr::Var(target_var)) => {
                var.shift_and_compare_impl(ctx, subst_ctx, target_var, target_subctx)
            }
            (Expr::App(app), Expr::App(target_app)) => app.substitute_and_shift_and_compare_impl(
                ctx,
                args,
                subst_ctx,
                target_app,
                target_subctx,
            ),
            (Expr::Lambda(lambda), Expr::Lambda(target_lambda)) => lambda
                .substitute_and_shift_and_compare_impl(
                    ctx,
                    args,
                    subst_ctx,
                    target_lambda,
                    target_subctx,
                ),
            (Expr::Lambda(lambda), _) => {
                if let Some(cmb) = lambda.try_convert_to_combinator(ctx)? {
                    cmb.substitute_and_shift_and_compare_impl(
                        ctx,
                        args,
                        subst_ctx,
                        target,
                        target_subctx,
                    )
                } else {
                    Ok(false)
                }
            }
            (_, Expr::Lambda(target_lambda)) => {
                if let Some(target_cmb) = target_lambda.try_convert_to_combinator(target_subctx)? {
                    self.substitute_and_shift_and_compare_impl(
                        ctx,
                        args,
                        subst_ctx,
                        &target_cmb,
                        target_subctx,
                    )
                } else {
                    Ok(false)
                }
            }
            (Expr::Cast(cast), Expr::Cast(target_cast)) => cast
                .substitute_and_shift_and_compare_impl(
                    ctx,
                    args,
                    subst_ctx,
                    target_cast,
                    target_subctx,
                ),
            _ => Ok(false),
        }
    }
}

pub trait HasType {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr>;

    fn has_type(&self, expected_type: &mut Expr, ctx: &MetaLogicContext) -> Result<bool> {
        let mut expr_type = self.get_type(ctx)?;
        Ok(expr_type.is_defeq(expected_type, ctx)?.is_some())
    }
}

impl HasType for Expr {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        match self {
            Expr::Placeholder => Ok(Expr::Placeholder),
            Expr::Var(var) => var.get_type(ctx),
            Expr::App(app) => app.get_type(ctx),
            Expr::Lambda(lambda) => lambda.get_type(ctx),
            Expr::Cast(cast) => cast.get_type(ctx),
        }
    }
}

pub trait CanParse: Sized {
    fn parse(s: &str, ctx: &MetaLogicContext) -> Result<Self>;
}

impl CanParse for Expr {
    fn parse(s: &str, ctx: &MetaLogicContext) -> Result<Self> {
        ParsingContext::parse(s, ctx, |parsing_context| parsing_context.parse_expr())
    }
}

pub trait CanPrint {
    fn print(&self, ctx: &MetaLogicContext) -> String;
}

impl CanPrint for Expr {
    fn print(&self, ctx: &MetaLogicContext) -> String {
        let mut result = String::new();
        PrintingContext::print(&mut result, ctx, |printing_context| {
            printing_context.print_expr(self)
        })
        .unwrap();
        result
    }
}

impl HasType for Var {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        let Var(idx) = self;
        Ok(ctx.get_var(*idx).type_expr.shifted_from_var(ctx, *idx))
    }
}

pub type AppExpr = App<Expr, Arg>;

impl HasType for AppExpr {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        // Finding the result type of an application is surprisingly tricky because the
        // application itself does not include the type parameters of its function. Instead,
        // to determine the property we need to match the type of the function against a term that
        // denotes a generic pi type. Then we apply the property to the argument of the application.
        if self.body.is_empty() {
            return Ok(Expr::Placeholder);
        }
        match self.get_type_parts(ctx, false)? {
            TypeArgs::Indep(_, codomain) => Ok(codomain),
            TypeArgs::Dep(_, prop) => Ok(prop.apply(self.param.clone(), ctx)),
        }
    }
}

pub trait IsApp {
    fn beta_reduce(&mut self, ctx: &impl Context) -> Option<Expr>;
    fn beta_reduce_if_trivial(&mut self, ctx: &impl ParamContext<Param>) -> Option<Expr>;

    fn eta_reduce<Ctx: Context>(&mut self, ctx: &Ctx, body_ctx: &Ctx) -> Option<Expr>;

    fn get_type_parts(&self, ctx: &MetaLogicContext, reduce_all: bool) -> Result<TypeArgs>;
    fn check_domain(
        &self,
        ctx: &MetaLogicContext,
        domain: &mut Expr,
        fun_type: &Expr,
    ) -> Result<()>;
}

impl IsApp for AppExpr {
    fn beta_reduce(&mut self, ctx: &impl Context) -> Option<Expr> {
        if let Expr::Lambda(lambda) = &mut self.body {
            Some(take(lambda).apply(take(&mut self.param), ctx))
        } else {
            None
        }
    }

    fn beta_reduce_if_trivial(&mut self, ctx: &impl ParamContext<Param>) -> Option<Expr> {
        if let Expr::Lambda(lambda) = &mut self.body {
            if self.param.expr.is_small() {
                return Some(take(lambda).apply(take(&mut self.param), ctx));
            }
            if let Some(const_body) = lambda.extract_body_if_const(ctx) {
                return Some(const_body);
            }
        }
        None
    }

    fn eta_reduce<Ctx: Context>(&mut self, ctx: &Ctx, body_ctx: &Ctx) -> Option<Expr> {
        if let Expr::Var(Var(-1)) = self.param.expr {
            if self.body.valid_in_superctx(body_ctx, ctx) {
                let mut eta_reduced = take(&mut self.body);
                eta_reduced.shift_to_supercontext(body_ctx, ctx);
                return Some(eta_reduced);
            }
        }
        None
    }

    fn get_type_parts(&self, ctx: &MetaLogicContext, reduce_all: bool) -> Result<TypeArgs> {
        let fun = &self.body;
        let arg = &self.param;
        let mut fun_type = fun.get_type(ctx)?;
        fun_type.reduce(ctx, !reduce_all, -1)?;
        if let Some((domain, codomain)) = fun_type.match_indep_type(StandardTypeCtorKind::Pi, ctx) {
            let mut domain = domain.clone();
            self.check_domain(ctx, &mut domain, &fun_type)?;
            Ok(TypeArgs::Indep(domain, codomain.clone()))
        } else if let Some((domain, prop)) = fun_type.match_dep_type(StandardTypeCtorKind::Pi, ctx)
        {
            let mut domain = domain.clone();
            self.check_domain(ctx, &mut domain, &fun_type)?;
            Ok(TypeArgs::Dep(domain, prop.clone()))
        } else {
            let fun_str = fun.print(ctx);
            let fun_type_str = fun_type.print(ctx);
            let arg_str = arg.expr.print(ctx);
            Err(anyhow!("invalid application: «{fun_str} : {fun_type_str}»\nis being applied to «{arg_str}» but is not a function"))
        }
    }

    fn check_domain(
        &self,
        ctx: &MetaLogicContext,
        domain: &mut Expr,
        fun_type: &Expr,
    ) -> Result<()> {
        let fun = &self.body;
        let arg = &self.param;
        let mut arg_type = arg.expr.get_type(ctx)?;
        if arg_type.is_defeq(domain, ctx)?.is_some() {
            Ok(())
        } else {
            let fun_str = fun.print(ctx);
            let fun_type_str = fun_type.print(ctx);
            let domain_str = domain.print(ctx);
            let arg_str = arg.expr.print(ctx);
            let arg_type_str = arg_type.print(ctx);
            Err(anyhow!("application type mismatch: «{fun_str} : {fun_type_str}»\nwith domain «{domain_str}»\ncannot be applied to «{arg_str} : {arg_type_str}»"))
        }
    }
}

pub enum TypeArgs {
    Indep(Expr, Expr),
    Dep(Expr, Expr),
}

pub type LambdaExpr = Lambda<Param, Expr>;

impl HasType for LambdaExpr {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        ctx.with_local(&self.param, |body_ctx| {
            let body_type = self.body.get_type(body_ctx)?;
            Expr::get_fun_type(&self.param, body_type, ctx, body_ctx)
        })
    }
}

pub trait IsLambda {
    fn apply(self, arg: Arg, ctx: &impl Context) -> Expr;

    fn extract_body_if_const(&mut self, ctx: &impl ParamContext<Param>) -> Option<Expr>;

    fn try_convert_to_combinator<Ctx: ComparisonContext>(&self, ctx: &Ctx) -> Result<Option<Expr>> {
        if let Some(metalogic_ctx) = ctx.as_metalogic_context() {
            if metalogic_ctx.use_combinators() {
                let expr = self.convert_to_combinator(metalogic_ctx)?;
                //dbg!(expr.print(metalogic_ctx));
                return Ok(Some(expr));
            }
        }
        Ok(None)
    }

    fn convert_to_combinator(&self, ctx: &MetaLogicContext) -> Result<Expr>;
}

impl IsLambda for LambdaExpr {
    fn apply(self, arg: Arg, ctx: &impl Context) -> Expr {
        let mut expr = self.body;
        expr.substitute(&mut [arg.expr], true, ctx);
        expr
    }

    fn extract_body_if_const(&mut self, ctx: &impl ParamContext<Param>) -> Option<Expr> {
        ctx.with_local(&self.param, |body_ctx| {
            if self.body.valid_in_superctx(body_ctx, ctx) {
                let mut const_body = take(&mut self.body);
                const_body.shift_to_supercontext(body_ctx, ctx);
                Some(const_body)
            } else {
                None
            }
        })
    }

    fn convert_to_combinator(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        create_combinator_app(&self.param, &self.body, ctx)
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum StandardTypeCtorKind {
    Pi,
    Sigma,
}

fn create_combinator_app(param: &Param, body: &Expr, ctx: &MetaLogicContext) -> Result<Expr> {
    ctx.with_local(param, |body_ctx| {
        //dbg!(body.print(body_ctx));

        if let Some(shifted_body) = body.shifted_to_supercontext(body_ctx, ctx) {
            let body_type = shifted_body.get_type(ctx)?;
            return Ok(Expr::multi_app(
                ctx.config().const_cmb.clone(),
                [
                    Arg::explicit(param.type_expr.clone()),
                    Arg::implicit(body_type),
                    Arg::explicit(shifted_body),
                ],
            ));
        }

        match body {
            Expr::Var(Var(-1)) => Ok(Expr::app(
                ctx.config().id_cmb.clone(),
                Arg::explicit(param.type_expr.clone()),
            )),
            Expr::App(app) => {
                let fun = &app.body;
                let arg = &app.param.expr;
                if let Expr::Var(Var(-1)) = arg {
                    // If the expression can be eta-reduced, do that instead of outputting a
                    // combinator.
                    if let Some(shifted_fun) = fun.shifted_to_supercontext(body_ctx, ctx) {
                        return Ok(shifted_fun);
                    }
                }
                let fun_lambda = Expr::lambda(param.clone(), fun.clone());
                let arg_lambda = Expr::lambda(param.clone(), arg.clone());
                match app.get_type_parts(body_ctx, true)? {
                    TypeArgs::Indep(mut domain, mut codomain) => {
                        if domain.valid_in_superctx(body_ctx, ctx)
                            && codomain.valid_in_superctx(body_ctx, ctx)
                        {
                            domain.shift_to_supercontext(body_ctx, ctx);
                            codomain.shift_to_supercontext(body_ctx, ctx);
                            Ok(Expr::multi_app(
                                ctx.config().subst_cmb.clone(),
                                [
                                    Arg::implicit(param.type_expr.clone()),
                                    Arg::implicit(domain),
                                    Arg::implicit(codomain),
                                    Arg::explicit(fun_lambda),
                                    Arg::explicit(arg_lambda),
                                ],
                            ))
                        } else {
                            let prop1 = Expr::lambda(param.clone(), domain.clone());
                            let rel2 = Expr::lambda(
                                param.clone(),
                                Expr::const_lambda(domain, codomain, body_ctx),
                            );
                            Ok(Expr::multi_app(
                                ctx.config().substd_cmb.clone(),
                                [
                                    Arg::implicit(param.type_expr.clone()),
                                    Arg::implicit(prop1),
                                    Arg::implicit(rel2),
                                    Arg::explicit(fun_lambda),
                                    Arg::explicit(arg_lambda),
                                ],
                            ))
                        }
                    }
                    TypeArgs::Dep(domain, prop) => {
                        let prop1 = Expr::lambda(param.clone(), domain);
                        let rel2 = Expr::lambda(param.clone(), prop);
                        Ok(Expr::multi_app(
                            ctx.config().substd_cmb.clone(),
                            [
                                Arg::implicit(param.type_expr.clone()),
                                Arg::implicit(prop1),
                                Arg::implicit(rel2),
                                Arg::explicit(fun_lambda),
                                Arg::explicit(arg_lambda),
                            ],
                        ))
                    }
                }
            }
            Expr::Lambda(lambda) => {
                let body_cmb = lambda.convert_to_combinator(body_ctx)?;
                //dbg!(body_cmb.print(body_ctx));
                create_combinator_app(param, &body_cmb, ctx)
            }
            _ => unreachable!("constant body should have been detected"),
        }
    })
}

#[derive(Clone, Default)]
pub struct Param {
    pub name: Option<Symbol>,
    pub type_expr: Expr,
    pub implicit: bool,
}

impl NamedObject<Option<Symbol>> for Param {
    fn get_name(&self) -> Option<Symbol> {
        self.name
    }
}

impl PartialEq for Param {
    fn eq(&self, other: &Self) -> bool {
        self.type_expr == other.type_expr
    }
}

impl Debug for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.implicit {
            f.write_str("{")?;
        }
        self.name.fmt(f)?;
        f.write_str(":")?;
        self.type_expr.fmt(f)?;
        if self.implicit {
            f.write_str("}")?;
        }
        Ok(())
    }
}

impl ContextObject for Param {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        self.type_expr.shift_impl(start, end, shift);
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        Param {
            name: self.name,
            type_expr: self.type_expr.shifted_impl(start, end, shift),
            implicit: self.implicit,
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        self.type_expr.count_refs_impl(start, ref_counts);
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        self.type_expr.has_refs_impl(start, end)
    }
}

impl ContextObjectWithSubst<Expr> for Param {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [Expr],
        ref_counts: &mut [usize],
    ) {
        self.type_expr
            .substitute_impl(shift_start, args_start, args, ref_counts);
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithCmp<Ctx> for Param {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        self.type_expr
            .shift_and_compare_impl(ctx, orig_ctx, &target.type_expr, target_subctx)
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithSubstCmp<Expr, Ctx> for Param {
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [Expr],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        self.type_expr.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.type_expr,
            target_subctx,
        )
    }
}

impl CanPrint for Param {
    fn print(&self, ctx: &MetaLogicContext) -> String {
        let mut result = String::new();
        PrintingContext::print(&mut result, ctx, |printing_context| {
            printing_context.print_param(self)
        })
        .unwrap();
        result
    }
}

#[derive(Clone, Default)]
pub struct Arg {
    pub expr: Expr,
    pub implicit: bool,
    pub match_all: bool,
}

impl Arg {
    pub fn explicit(expr: Expr) -> Self {
        Arg {
            expr,
            implicit: false,
            match_all: false,
        }
    }

    pub fn implicit(expr: Expr) -> Self {
        Arg {
            expr,
            implicit: true,
            match_all: false,
        }
    }
}

impl PartialEq for Arg {
    fn eq(&self, other: &Self) -> bool {
        self.expr == other.expr
    }
}

impl Debug for Arg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.implicit {
            f.write_str("{")?;
        }
        self.expr.fmt(f)?;
        if self.implicit {
            f.write_str("}")?;
        }
        Ok(())
    }
}

impl ContextObject for Arg {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        self.expr.shift_impl(start, end, shift);
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        Arg {
            expr: self.expr.shifted_impl(start, end, shift),
            ..*self
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        self.expr.count_refs_impl(start, ref_counts);
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        self.expr.has_refs_impl(start, end)
    }
}

impl ContextObjectWithSubst<Expr> for Arg {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [Expr],
        ref_counts: &mut [usize],
    ) {
        self.expr
            .substitute_impl(shift_start, args_start, args, ref_counts);
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithCmp<Ctx> for Arg {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if self.match_all {
            return Ok(true);
        }
        self.expr
            .shift_and_compare_impl(ctx, orig_ctx, &target.expr, target_subctx)
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithSubstCmp<Expr, Ctx> for Arg {
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [Expr],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if self.match_all {
            return Ok(true);
        }
        self.expr.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.expr,
            target_subctx,
        )
    }
}

#[derive(Clone, PartialEq)]
pub struct CastExpr {
    pub expr: Expr,
    pub target_type: Expr,
    pub type_defeq: DefinitionalEquality,
}

impl Debug for CastExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.expr.fmt(f)?;
        f.write_str("↑")?;
        Ok(())
    }
}

impl ContextObject for CastExpr {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        self.expr.shift_impl(start, end, shift);
        self.target_type.shift_impl(start, end, shift);
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        CastExpr {
            expr: self.expr.shifted_impl(start, end, shift),
            target_type: self.target_type.shifted_impl(start, end, shift),
            type_defeq: self.type_defeq.clone(),
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        self.expr.count_refs_impl(start, ref_counts);
        self.target_type.count_refs_impl(start, ref_counts);
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        self.expr.has_refs_impl(start, end) || self.target_type.has_refs_impl(start, end)
    }
}

impl ContextObjectWithSubst<Expr> for CastExpr {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [Expr],
        ref_counts: &mut [usize],
    ) {
        self.expr
            .substitute_impl(shift_start, args_start, args, ref_counts);
        self.target_type
            .substitute_impl(shift_start, args_start, args, ref_counts);
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithCmp<Ctx> for CastExpr {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self.target_type.shift_and_compare_impl(
            ctx,
            orig_ctx,
            &target.target_type,
            target_subctx,
        )? {
            return Ok(false);
        }

        self.expr
            .shift_and_compare_impl(ctx, orig_ctx, &target.expr, target_subctx)
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithSubstCmp<Expr, Ctx> for CastExpr {
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [Expr],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self.target_type.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.target_type,
            target_subctx,
        )? {
            return Ok(false);
        }

        self.expr.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.expr,
            target_subctx,
        )
    }
}

impl HasType for CastExpr {
    fn get_type(&self, _: &MetaLogicContext) -> Result<Expr> {
        Ok(self.target_type.clone())
    }
}

// Definitional equality is given by reduction of both sides to the same value.
// Note that this relationship is not transitive unless reduction traces are unique (so they can be
// canceled) or at least confluent (so they can be extended to a common target).
#[derive(Clone, PartialEq, Default)]
pub struct DefinitionalEquality {
    pub left: ReductionTrace,
    pub right: ReductionTrace,
}

impl DefinitionalEquality {
    pub fn trivial() -> Self {
        DefinitionalEquality {
            left: ReductionTrace::new(),
            right: ReductionTrace::new(),
        }
    }

    pub fn is_trivial(&self) -> bool {
        self.left.is_empty() && self.right.is_empty()
    }
}

pub type ReductionTrace = Vec<ReductionStep>;

#[derive(Clone, PartialEq)]
pub enum ReductionStep {
    AppFunReduction(ReductionTrace),
    AppArgReduction(ReductionTrace),
    BetaReduction,
    LambdaParamTypeReduction(ReductionTrace),
    LambdaBodyReduction(ReductionTrace),
    EtaReduction,
    CastExprReduction(ReductionTrace),
    ReductionRuleApplication, // TODO
}

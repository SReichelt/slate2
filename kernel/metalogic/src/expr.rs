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

    pub fn explicit_app(fun: Expr, arg: Expr) -> Self {
        Self::app(
            fun,
            Arg {
                expr: arg,
                implicit: false,
                match_all: false,
            },
        )
    }

    pub fn multi_app(mut fun: Expr, args: SmallVec<[Arg; INLINE_PARAMS]>) -> Self {
        for arg in args {
            fun = Self::app(fun, arg);
        }
        fun
    }

    pub fn explicit_multi_app(mut fun: Expr, args: SmallVec<[Expr; INLINE_PARAMS]>) -> Self {
        for arg in args {
            fun = Self::explicit_app(fun, arg);
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

    pub fn multi_apply(mut self, args: SmallVec<[Arg; INLINE_PARAMS]>, ctx: &impl Context) -> Self {
        for arg in args {
            self = Self::apply(self, arg, ctx);
        }
        self
    }

    pub fn lambda(param: Param, body: Expr) -> Self {
        Expr::Lambda(Box::new(Lambda { param, body }))
    }

    pub fn multi_lambda(params: SmallVec<[Param; INLINE_PARAMS]>, mut body: Expr) -> Self {
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

    pub fn let_binding(
        params: SmallVec<[Param; INLINE_PARAMS]>,
        args: SmallVec<[Arg; INLINE_PARAMS]>,
        body: Expr,
    ) -> Self {
        Expr::multi_app(Expr::multi_lambda(params, body), args)
    }

    pub fn is_small(&self) -> bool {
        match self {
            Expr::Placeholder => true,
            Expr::Var(_) => true,
            Expr::App(_) => false,
            Expr::Lambda(_) => false,
        }
    }

    pub fn reduce_all(&mut self, ctx: &MetaLogicContext) -> Result<bool> {
        self.reduce(ctx, false, -1)
    }

    pub fn reduce(
        &mut self,
        ctx: &MetaLogicContext,
        head_only: bool,
        mut max_depth: i32,
    ) -> Result<bool> {
        if self.is_empty() {
            return Ok(false);
        }

        if max_depth >= 0 {
            if max_depth == 0 {
                return Ok(false);
            }
            max_depth -= 1;
        }

        let apply_reduction_rules = ctx.options().reduce_with_reduction_rules;

        let mut reduced = false;

        loop {
            reduced |= self.reduce_step_impl(ctx, head_only, max_depth)?;

            if apply_reduction_rules {
                if let Some(applied_rule) = self.apply_reduction_rule(ctx)? {
                    if applied_rule {
                        reduced = true;
                        continue;
                    }
                } else if head_only {
                    // Indeterminate result with not-fully-reduced arguments: reduce them and retry.
                    if self.reduce_step_impl(ctx, false, max_depth)? {
                        reduced = true;
                        if let Some(true) = self.apply_reduction_rule(ctx)? {
                            continue;
                        }
                    }
                }
            }

            return Ok(reduced);
        }
    }

    fn reduce_step_impl(
        &mut self,
        ctx: &MetaLogicContext,
        head_only: bool,
        max_depth: i32,
    ) -> Result<bool> {
        let mut reduced = false;

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
                        reduced = true;
                        continue;
                    }

                    reduced |= app.body.reduce(ctx, head_only, max_depth)?;

                    if !head_only {
                        // Reduction of function may have made beta reduction possible.
                        if let Some(beta_reduced) = app.beta_reduce_if_trivial(ctx) {
                            *self = beta_reduced;
                            reduced = true;
                            continue;
                        }

                        reduced |= app.param.expr.reduce(ctx, head_only, max_depth)?;
                    }

                    // Now always beta-reduce if possible.
                    if let Some(beta_reduced) = app.beta_reduce(ctx) {
                        *self = beta_reduced;
                        reduced = true;
                        continue;
                    }
                }
                Expr::Lambda(lambda) => {
                    if !head_only {
                        reduced |= lambda.param.type_expr.reduce(ctx, head_only, max_depth)?;

                        if let Some(eta_reduced) =
                            ctx.with_local(&lambda.param, |body_ctx| -> Result<Option<Expr>> {
                                reduced |= lambda.body.reduce(&body_ctx, head_only, max_depth)?;

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
                            reduced = true;
                            continue;
                        }
                    }
                }
            }

            return Ok(reduced);
        }
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

    pub fn is_defeq(&mut self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<bool> {
        if self.compare(expr, ctx)? {
            return Ok(true);
        }

        // We could first reduce just enough to be sure that the two expressions cannot possibly be
        // definitionally equal, but `is_defeq` is really only meant to be called for verification,
        // not for matching.
        self.reduce_all(ctx)?;
        expr.reduce_all(ctx)?;

        self.compare(expr, ctx)
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
                        lambda.body.convert_to_combinators(&body_ctx, max_depth)
                    })?;

                    *self = lambda.convert_to_combinator(ctx)?;
                    continue;
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

    pub fn match_expr_1<Ctx: ComparisonContext>(
        &self,
        ctx: &Ctx,
        match_param: Param,
        match_expr: &Expr,
    ) -> Result<Option<Expr>> {
        if let Some(mut result_vec) = self.match_expr(ctx, &[match_param], match_expr)? {
            Ok(result_vec.pop())
        } else {
            Ok(None)
        }
    }

    pub fn match_expr_2<Ctx: ComparisonContext>(
        &self,
        ctx: &Ctx,
        match_param_1: Param,
        match_param_2: Param,
        match_expr: &Expr,
    ) -> Result<Option<(Expr, Expr)>> {
        if let Some(mut result_vec) =
            self.match_expr(ctx, &[match_param_1, match_param_2], match_expr)?
        {
            let result_2 = result_vec.pop().unwrap();
            let result_1 = result_vec.pop().unwrap();
            Ok(Some((result_1, result_2)))
        } else {
            Ok(None)
        }
    }

    pub fn get_fun_type(param: &Param, body_type: Expr, ctx: &MetaLogicContext) -> Result<Expr> {
        let prop = Expr::lambda(param.clone(), body_type);
        ctx.lambda_handler().get_dep_type(
            param.type_expr.clone(),
            prop,
            DependentTypeCtorKind::Pi,
            ctx.as_minimal(),
        )
    }

    pub fn match_generic_indep_type(
        &self,
        kind: DependentTypeCtorKind,
        ctx: &MetaLogicContext,
    ) -> Option<(Expr, Expr)> {
        if *self != Expr::Placeholder {
            let min_ctx = ctx.as_minimal();
            if let Ok((domain_param, codomain_param, generic_indep_type)) =
                ctx.lambda_handler().get_generic_indep_type(kind, min_ctx)
            {
                if let Ok(Some((domain, codomain))) =
                    self.match_expr_2(&min_ctx, domain_param, codomain_param, &generic_indep_type)
                {
                    // If the codomain is a placeholder, we don't really know whether this should
                    // be a dependent type instead.
                    if !codomain.is_empty() {
                        return Some((domain, codomain));
                    }
                }
            }
        }
        None
    }

    pub fn match_generic_dep_type(
        &self,
        kind: DependentTypeCtorKind,
        ctx: &MetaLogicContext,
    ) -> Option<(Expr, Expr)> {
        if *self != Expr::Placeholder {
            let min_ctx = ctx.as_minimal();
            if let Ok((domain_param, prop_param, generic_dep_type)) =
                ctx.lambda_handler().get_generic_dep_type(kind, min_ctx)
            {
                if let Ok(result) =
                    self.match_expr_2(&min_ctx, domain_param, prop_param, &generic_dep_type)
                {
                    return result;
                }
            }
        }
        None
    }

    pub fn match_generic_dep_type_as_lambda(
        &self,
        kind: DependentTypeCtorKind,
        convert_to_lambda: bool,
        ctx: &MetaLogicContext,
    ) -> Option<LambdaExpr> {
        if let Some((domain, mut prop)) = self.match_generic_dep_type(kind, ctx) {
            if let Expr::Lambda(lambda) = prop {
                return Some(*lambda);
            } else if convert_to_lambda {
                let param = Param {
                    name: None,
                    type_expr: domain,
                    implicit: false,
                };
                ctx.with_local(&param, |subctx| {
                    prop.shift_to_subcontext(ctx, subctx);
                });
                return Some(Lambda {
                    param,
                    body: Expr::explicit_app(prop, Expr::var(-1)),
                });
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
                type_1.match_generic_dep_type_as_lambda(DependentTypeCtorKind::Pi, true, ctx),
                type_2.match_generic_dep_type_as_lambda(DependentTypeCtorKind::Pi, true, ctx),
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
        }
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        match self {
            Expr::Placeholder => Expr::Placeholder,
            Expr::Var(var) => Expr::Var(var.shifted_impl(start, end, shift)),
            Expr::App(app) => Expr::App(Box::new(app.shifted_impl(start, end, shift))),
            Expr::Lambda(lambda) => Expr::Lambda(Box::new(lambda.shifted_impl(start, end, shift))),
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        match self {
            Expr::Placeholder => {}
            Expr::Var(var) => var.count_refs_impl(start, ref_counts),
            Expr::App(app) => app.count_refs_impl(start, ref_counts),
            Expr::Lambda(lambda) => lambda.count_refs_impl(start, ref_counts),
        }
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        match self {
            Expr::Placeholder => false,
            Expr::Var(var) => var.has_refs_impl(start, end),
            Expr::App(app) => app.has_refs_impl(start, end),
            Expr::Lambda(lambda) => lambda.has_refs_impl(start, end),
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
            _ => Ok(false),
        }
    }
}

pub trait HasType {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr>;

    fn has_type(&self, expected_type: &mut Expr, ctx: &MetaLogicContext) -> Result<bool> {
        let mut expr_type = self.get_type(ctx)?;
        expr_type.is_defeq(expected_type, ctx)
    }
}

impl HasType for Expr {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        match self {
            Expr::Placeholder => Ok(Expr::Placeholder),
            Expr::Var(var) => var.get_type(ctx),
            Expr::App(app) => app.get_type(ctx),
            Expr::Lambda(lambda) => lambda.get_type(ctx),
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
            printing_context.print_expr(&self)
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
        let (_, prop) = self.get_type_parts(ctx, false)?;
        Ok(prop.apply(self.param.clone(), ctx))
    }
}

pub trait IsApp {
    fn beta_reduce(&mut self, ctx: &impl Context) -> Option<Expr>;
    fn beta_reduce_if_trivial(&mut self, ctx: &impl ParamContext<Param>) -> Option<Expr>;

    fn eta_reduce<Ctx: Context>(&mut self, ctx: &Ctx, body_ctx: &Ctx) -> Option<Expr>;

    fn get_type_parts(&self, ctx: &MetaLogicContext, reduce_all: bool) -> Result<(Expr, Expr)>;
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

    fn get_type_parts(&self, ctx: &MetaLogicContext, reduce_all: bool) -> Result<(Expr, Expr)> {
        let fun = &self.body;
        let arg = &self.param;
        let mut fun_type = fun.get_type(ctx)?;
        fun_type.reduce(ctx, !reduce_all, -1)?;
        if let Some((mut domain, prop)) =
            fun_type.match_generic_dep_type(DependentTypeCtorKind::Pi, ctx)
        {
            let mut arg_type = arg.expr.get_type(ctx)?;
            if arg_type.is_defeq(&mut domain, ctx)? {
                Ok((domain, prop))
            } else {
                let fun_str = fun.print(ctx);
                let fun_type_str = fun_type.print(ctx);
                let domain_str = domain.print(ctx);
                let arg_str = arg.expr.print(ctx);
                let arg_type_str = arg_type.print(ctx);
                Err(anyhow!("application type mismatch: «{fun_str} : {fun_type_str}»\nwith domain «{domain_str}»\ncannot be applied to «{arg_str} : {arg_type_str}»"))
            }
        } else {
            let fun_str = fun.print(ctx);
            let fun_type_str = fun_type.print(ctx);
            let arg_str = arg.expr.print(ctx);
            Err(anyhow!("invalid application: «{fun_str} : {fun_type_str}»\nis being applied to «{arg_str}» but is not a function"))
        }
    }
}

pub type LambdaExpr = Lambda<Param, Expr>;

impl HasType for LambdaExpr {
    fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        ctx.with_local(&self.param, |body_ctx| {
            let body_type = self.body.get_type(body_ctx)?;
            Expr::get_fun_type(&self.param, body_type, ctx)
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

fn create_combinator_app(param: &Param, body: &Expr, ctx: &MetaLogicContext) -> Result<Expr> {
    ctx.with_local(&param, |body_ctx| {
        //dbg!(body.print(body_ctx));

        if let Some(shifted_body) = body.shifted_to_supercontext(body_ctx, ctx) {
            let body_type = shifted_body.get_type(ctx)?;
            let cmb = ctx.lambda_handler().get_const_cmb(
                param.type_expr.clone(),
                body_type,
                ctx.as_minimal(),
            )?;
            return Ok(Expr::explicit_app(cmb, shifted_body));
        }

        match body {
            Expr::Var(Var(-1)) => ctx
                .lambda_handler()
                .get_id_cmb(param.type_expr.clone(), ctx.as_minimal()),
            Expr::App(app) => {
                if let Expr::Var(Var(-1)) = app.param.expr {
                    // If the expression can be eta-reduced, do that instead of outputting a
                    // combinator.
                    if let Some(shifted_fun) = app.body.shifted_to_supercontext(body_ctx, ctx) {
                        return Ok(shifted_fun);
                    }
                }
                let cmb = get_subst_cmb(param, ctx, app, body_ctx)?;
                let fun_lambda = Expr::lambda(param.clone(), app.body.clone());
                let arg_lambda = Expr::lambda(param.clone(), app.param.expr.clone());
                Ok(Expr::explicit_multi_app(
                    cmb,
                    smallvec![fun_lambda, arg_lambda],
                ))
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

fn get_subst_cmb(
    param: &Param,
    ctx: &MetaLogicContext,
    app: &AppExpr,
    body_ctx: &MetaLogicContext,
) -> Result<Expr> {
    let (domain, prop) = app.get_type_parts(body_ctx, true)?;
    let prop1 = Expr::lambda(param.clone(), domain);
    let rel2 = Expr::lambda(param.clone(), prop);
    ctx.lambda_handler()
        .get_subst_cmb(param.type_expr.clone(), prop1, rel2, ctx.as_minimal())
}

#[derive(Clone, Default)]
pub struct Param {
    pub name: Option<Symbol>,
    pub type_expr: Expr,
    pub implicit: bool,
}

impl NamedObject<Symbol> for Param {
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
            name: self.name.clone(),
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
            printing_context.print_param(&self)
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
            implicit: self.implicit,
            match_all: self.match_all,
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
        if self.match_all || target.match_all {
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
        if self.match_all || target.match_all {
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

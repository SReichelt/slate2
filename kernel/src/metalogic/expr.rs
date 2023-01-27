use std::{
    fmt::{self, Debug},
    rc::Rc,
};

use anyhow::{anyhow, Result};
use smallvec::{smallvec, SmallVec};

use super::{metalogic::*, parse::*, print::*};

use crate::generic::{context::*, context_object::*, expr_parts::*};

#[derive(Clone, PartialEq)]
pub enum Expr {
    Var(Var), // includes primitive constants
    App(Box<AppExpr>),
    Lambda(Box<LambdaExpr>),
}

impl Expr {
    pub fn var(idx: VarIndex) -> Self {
        Expr::Var(Var(idx))
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Expr::Var(_))
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
            let mut expr = lambda.body;
            expr.substitute(&mut [arg.expr], true, ctx);
            expr
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

    pub fn get_const_app_info(&self) -> Option<(VarIndex, usize)> {
        let mut len = 0;
        let mut fun = self;
        while let Expr::App(app) = fun {
            len += 1;
            fun = &app.body;
        }
        if let Expr::Var(Var(var_idx)) = fun {
            if *var_idx >= 0 {
                return Some((*var_idx, len));
            }
        }
        None
    }

    pub fn parse(s: &str, ctx: &MetaLogicContext) -> Result<Self> {
        ParsingContext::parse(s, ctx, |parsing_context| parsing_context.parse_expr())
    }

    pub fn print(&self, ctx: &MetaLogicContext) -> String {
        let mut result = String::new();
        PrintingContext::print(&mut result, ctx, |printing_context| {
            printing_context.print_expr(&self)
        })
        .unwrap();
        result
    }

    pub fn reduce(&mut self, ctx: &MetaLogicContext, mut max_depth: i32) -> Result<bool> {
        if max_depth >= 0 {
            if max_depth == 0 {
                return Ok(false);
            }
            max_depth -= 1;
        }

        let mut reduced = false;

        loop {
            match self {
                Expr::Var(_) => {}
                Expr::App(app) => {
                    reduced |= app.param.expr.reduce(ctx, max_depth)?;
                    reduced |= app.body.reduce(ctx, max_depth)?;

                    if let Expr::Lambda(lambda) = &mut app.body {
                        let mut expr = std::mem::take(&mut lambda.body);
                        let arg = std::mem::take(&mut app.param.expr);
                        expr.substitute(&mut [arg], true, ctx);
                        *self = expr;
                        reduced = true;
                        continue;
                    }
                }
                Expr::Lambda(lambda) => {
                    reduced |= lambda.param.type_expr.reduce(ctx, max_depth)?;
                    reduced |= ctx.with_local(&lambda.param, |body_ctx| {
                        lambda.body.reduce(&body_ctx, max_depth)
                    })?;
                }
            }

            if self.apply_reduction_rule(ctx)? {
                reduced = true;
            } else {
                return Ok(reduced);
            }
        }
    }

    fn apply_reduction_rule(&mut self, ctx: &MetaLogicContext) -> Result<bool> {
        if let Some((const_idx, app_len)) = self.get_const_app_info() {
            for rule in &ctx.constants()[const_idx as usize].reduction_rules {
                if rule.body.source_app_len == app_len {
                    if let Some(mut args) = self.match_expr(ctx, &rule.params, &rule.body.source)? {
                        let mut expr = rule.body.target.clone();
                        expr.substitute(&mut args, true, ctx);
                        *self = expr;
                        return Ok(true);
                    }
                }
            }
        }

        Ok(false)
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
        let params_len = match_params.len();
        let mut args: SmallVec<[Expr; INLINE_PARAMS]> = smallvec![Expr::default(); params_len];
        let mut args_filled: SmallVec<[bool; INLINE_PARAMS]> = smallvec![false; params_len];
        if ctx.with_locals(match_params, |ctx_with_params| {
            match_expr.substitute_and_compare(
                ctx_with_params,
                &mut args,
                &mut args_filled,
                self,
                ctx,
            )
        })? {
            if args_filled.iter().all(|filled| *filled) {
                return Ok(Some(args));
            }
        }
        Ok(None)
    }

    pub fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        let mut result = self.get_unreduced_type(ctx)?;
        // There is a lot of potential for optimization here:
        // * Fully reducing all types is very suboptimal. We could have different reduction
        //   strengths instead.
        // * If we are determining the type of an application, then the types of the function and
        //   argument have already been reduced. Instead of ignoring that here, we could exploit it
        //   by skipping all subexpressions where no substitution occurs. The current behavior is
        //   especially problematic because the run time grows quadratically with expression size.
        result.reduce(ctx, -1)?;
        Ok(result)
    }

    fn get_unreduced_type(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        match self {
            Expr::Var(var) => Ok(var.get_type(ctx)),
            Expr::App(app) => {
                // Finding the result type of an application is surprisingly tricky because the
                // application itself does not include the type parameters of its function. Instead,
                // to determine the property we need to match the type of the actual function
                // argument against a term that denotes a sufficiently generic pi type. Then we
                // apply the property to the argument of the application.
                let fun = &app.body;
                let arg = &app.param;
                let fun_type = fun.get_type(ctx)?;
                let arg_type = arg.expr.get_type(ctx)?;
                if let Some(prop) = fun_type.get_prop_from_fun_type(arg_type, ctx)? {
                    Ok(Expr::apply(prop, arg.clone(), ctx))
                } else {
                    let fun_str = fun.print(ctx);
                    let fun_type_str = fun_type.print(ctx);
                    let arg_str = arg.expr.print(ctx);
                    let arg_type = arg.expr.get_type(ctx)?;
                    let arg_type_str = arg_type.print(ctx);
                    Err(anyhow!("application type mismatch: «{fun_str} : {fun_type_str}» cannot be applied to «{arg_str} : {arg_type_str}»"))
                }
            }
            Expr::Lambda(lambda) => ctx.with_local(&lambda.param, |body_ctx| {
                let body_type = lambda.body.get_type(body_ctx)?;
                let prop = Expr::lambda(lambda.param.clone(), body_type);
                ctx.lambda_handler().get_dep_type(
                    lambda.param.type_expr.clone(),
                    prop,
                    DependentTypeCtorKind::Pi,
                    ctx.as_minimal(),
                )
            }),
        }
    }

    fn get_prop_from_fun_type(
        &self,
        arg_type: Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Option<Expr>> {
        let (prop_param, cmp_fun_type) = ctx.lambda_handler().get_semi_generic_dep_type(
            arg_type,
            DependentTypeCtorKind::Pi,
            ctx.as_minimal(),
        )?;
        if let Some(mut prop_vec) = self.match_expr(ctx, &[prop_param], &cmp_fun_type)? {
            Ok(prop_vec.pop())
        } else {
            Ok(None)
        }
    }
}

impl Default for Expr {
    fn default() -> Self {
        Expr::Var(Var::default())
    }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Var(var) => var.fmt(f),
            Self::App(app) => app.fmt(f),
            Self::Lambda(lambda) => lambda.fmt(f),
        }
    }
}

impl ContextObject for Expr {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        match self {
            Expr::Var(var) => var.shift_impl(start, end, shift),
            Expr::App(app) => app.shift_impl(start, end, shift),
            Expr::Lambda(lambda) => lambda.shift_impl(start, end, shift),
        }
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        match self {
            Expr::Var(var) => Expr::Var(var.shifted_impl(start, end, shift)),
            Expr::App(app) => Expr::App(Box::new(app.shifted_impl(start, end, shift))),
            Expr::Lambda(lambda) => Expr::Lambda(Box::new(lambda.shifted_impl(start, end, shift))),
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        match self {
            Expr::Var(var) => var.count_refs_impl(start, ref_counts),
            Expr::App(app) => app.count_refs_impl(start, ref_counts),
            Expr::Lambda(lambda) => lambda.count_refs_impl(start, ref_counts),
        }
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        match self {
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
        args_filled: &mut [bool],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if let Expr::Var(var) = self {
            if let Some(result) =
                var.compare_subst_arg_impl(ctx, args, args_filled, subst_ctx, target, target_subctx)
            {
                return result;
            }
        }

        match (self, target) {
            (Expr::Var(var), Expr::Var(target_var)) => {
                var.shift_and_compare_impl(ctx, subst_ctx, target_var, target_subctx)
            }
            (Expr::App(app), Expr::App(target_app)) => app.substitute_and_shift_and_compare_impl(
                ctx,
                args,
                args_filled,
                subst_ctx,
                target_app,
                target_subctx,
            ),
            (Expr::Lambda(lambda), Expr::Lambda(target_lambda)) => lambda
                .substitute_and_shift_and_compare_impl(
                    ctx,
                    args,
                    args_filled,
                    subst_ctx,
                    target_lambda,
                    target_subctx,
                ),
            (Expr::Lambda(lambda), _) => {
                if let Some(cmb) = lambda.try_convert_to_combinator(ctx)? {
                    cmb.substitute_and_shift_and_compare_impl(
                        ctx,
                        args,
                        args_filled,
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
                        args_filled,
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

impl Var {
    pub fn get_type(&self, ctx: &MetaLogicContext) -> Expr {
        let Var(idx) = self;
        ctx.get_var(*idx).type_expr.shifted_from_var(ctx, *idx)
    }
}

pub type AppExpr = App<Expr, Arg>;
pub type LambdaExpr = Lambda<Param, Expr>;

impl LambdaExpr {
    fn try_convert_to_combinator<Ctx: ComparisonContext>(&self, ctx: &Ctx) -> Result<Option<Expr>> {
        if let Some(metalogic_ctx) = ctx.as_metalogic_context() {
            let expr = self.convert_to_combinator(metalogic_ctx)?;
            //dbg!(expr.print(metalogic_ctx));
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    fn convert_to_combinator(&self, ctx: &MetaLogicContext) -> Result<Expr> {
        Self::create_combinator_app(&self.param, &self.body, ctx)
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
                Expr::Var(Var(idx)) => {
                    debug_assert_eq!(*idx, -1); // Otherwise it was constant.
                    ctx.lambda_handler()
                        .get_id_cmb(param.type_expr.clone(), ctx.as_minimal())
                }
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
                    let cmb = Self::get_subst_cmb(param, ctx, fun, arg, body_ctx)?;
                    let fun_lambda = Expr::lambda(param.clone(), fun.clone());
                    let arg_lambda = Expr::lambda(param.clone(), arg.clone());
                    Ok(Expr::explicit_multi_app(
                        cmb,
                        smallvec![fun_lambda, arg_lambda],
                    ))
                }
                Expr::Lambda(lambda) => {
                    let body_cmb = lambda.convert_to_combinator(body_ctx)?;
                    //dbg!(body_cmb.print(body_ctx));
                    Self::create_combinator_app(param, &body_cmb, ctx)
                }
            }
        })
    }

    fn get_subst_cmb(
        param: &Param,
        ctx: &MetaLogicContext,
        fun: &Expr,
        arg: &Expr,
        body_ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        let fun_type = fun.get_type(body_ctx)?;
        let arg_type = arg.get_type(body_ctx)?;
        if let Some(fun_prop) = fun_type.get_prop_from_fun_type(arg_type.clone(), body_ctx)? {
            let prop1 = Expr::lambda(param.clone(), arg_type);
            let rel2 = Expr::lambda(param.clone(), fun_prop);
            ctx.lambda_handler().get_subst_cmb(
                param.type_expr.clone(),
                prop1,
                rel2,
                ctx.as_minimal(),
            )
        } else {
            let fun_str = fun.print(body_ctx);
            let fun_type_str = fun_type.print(body_ctx);
            let arg_str = arg.print(body_ctx);
            let arg_type_str = arg_type.print(body_ctx);
            Err(anyhow!("application type mismatch when converting to combinator: «{fun_str} : {fun_type_str}» cannot be applied to «{arg_str} : {arg_type_str}»"))
        }
    }
}

#[derive(Clone, Default)]
pub struct Param {
    pub name: Option<Rc<String>>,
    pub type_expr: Expr,
    pub implicit: bool,
}

impl NamedObject for Param {
    fn get_name(&self) -> Option<&str> {
        if let Some(name) = &self.name {
            Some(name)
        } else {
            None
        }
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
        f.write_str(self.get_name_or_placeholder())?;
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
        args_filled: &mut [bool],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        self.type_expr.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            args_filled,
            subst_ctx,
            &target.type_expr,
            target_subctx,
        )
    }
}

#[derive(Clone, Default)]
pub struct Arg {
    pub expr: Expr,
    pub implicit: bool,
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
        self.expr
            .shift_and_compare_impl(ctx, orig_ctx, &target.expr, target_subctx)
    }
}

impl<Ctx: ComparisonContext> ContextObjectWithSubstCmp<Expr, Ctx> for Arg {
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [Expr],
        args_filled: &mut [bool],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        self.expr.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            args_filled,
            subst_ctx,
            &target.expr,
            target_subctx,
        )
    }
}

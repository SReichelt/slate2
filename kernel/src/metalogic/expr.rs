use std::{
    fmt::{self, Debug},
    mem::take,
    rc::Rc,
};

use anyhow::{anyhow, Result};
use smallvec::{smallvec, SmallVec};

use super::{metalogic::*, parse::*, print::*};

use crate::generic::{context::*, context_object::*, expr_parts::*};

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
                Expr::Placeholder => {}
                Expr::Var(_) => {}
                Expr::App(app) => {
                    reduced |= app.param.expr.reduce(ctx, max_depth)?;
                    reduced |= app.body.reduce(ctx, max_depth)?;

                    if let Expr::Lambda(lambda) = &mut app.body {
                        *self = take(lambda).apply(take(&mut app.param), ctx);
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
                break;
            }
        }

        Ok(reduced)
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

    pub fn apply_one_reduction_rule(&mut self, ctx: &MetaLogicContext) -> Result<bool> {
        if self.apply_reduction_rule(ctx)? {
            Ok(true)
        } else if let Expr::App(app) = self {
            if app.body.apply_one_reduction_rule(ctx)? {
                if let Expr::Lambda(lambda) = &mut app.body {
                    *self = take(lambda).apply(take(&mut app.param), ctx);
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
            Expr::Placeholder => Ok(Expr::Placeholder),
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
                    Ok(prop.apply(arg.clone(), ctx))
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
                Self::get_fun_type(&lambda.param, body_type, ctx)
            }),
        }
    }

    fn get_fun_type(param: &Param, body_type: Expr, ctx: &MetaLogicContext) -> Result<Expr> {
        let prop = Expr::lambda(param.clone(), body_type);
        ctx.lambda_handler().get_dep_type(
            param.type_expr.clone(),
            prop,
            DependentTypeCtorKind::Pi,
            ctx.as_minimal(),
        )
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
        self.match_expr_1(ctx, prop_param, &cmp_fun_type)
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
                    if codomain != Expr::Placeholder {
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
        convert_to_lambda: bool,
        ctx: &MetaLogicContext,
    ) -> Option<LambdaExpr> {
        if *self != Expr::Placeholder {
            let min_ctx = ctx.as_minimal();
            if let Ok((domain_param, prop_param, generic_dep_type)) =
                ctx.lambda_handler().get_generic_dep_type(kind, min_ctx)
            {
                if let Ok(Some((domain, mut prop))) =
                    self.match_expr_2(&min_ctx, domain_param, prop_param, &generic_dep_type)
                {
                    if let Expr::Lambda(lambda) = prop {
                        return Some(*lambda);
                    } else if convert_to_lambda {
                        let param = Param {
                            name: None,
                            type_expr: domain,
                            implicit: false,
                        };
                        min_ctx.with_local(&param, |subctx| {
                            prop.shift_to_subcontext(&min_ctx, subctx);
                        });
                        return Some(Lambda {
                            param,
                            body: Expr::explicit_app(prop, Expr::var(-1)),
                        });
                    }
                }
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
                type_1.match_generic_dep_type(DependentTypeCtorKind::Pi, true, ctx),
                type_2.match_generic_dep_type(DependentTypeCtorKind::Pi, true, ctx),
            ) {
                if lambda_1.param.implicit != lambda_2.param.implicit {
                    let name_1 = lambda_1.param.get_name_or_placeholder();
                    let name_2 = lambda_1.param.get_name_or_placeholder();
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

impl Var {
    pub fn get_type(&self, ctx: &MetaLogicContext) -> Expr {
        let Var(idx) = self;
        ctx.get_var(*idx).type_expr.shifted_from_var(ctx, *idx)
    }
}

pub type AppExpr = App<Expr, Arg>;
pub type LambdaExpr = Lambda<Param, Expr>;

impl LambdaExpr {
    fn apply(self, arg: Arg, ctx: &impl Context) -> Expr {
        let mut expr = self.body;
        expr.substitute(&mut [arg.expr], true, ctx);
        expr
    }

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
                Expr::Var(Var(-1)) => ctx
                    .lambda_handler()
                    .get_id_cmb(param.type_expr.clone(), ctx.as_minimal()),
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
                _ => unreachable!("constant body should have been detected"),
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
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        self.expr.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.expr,
            target_subctx,
        )
    }
}

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
        let type_type = param.type_expr.get_type(ctx)?;
        let cmp_type_type = ctx.lambda_handler().get_universe_type()?;
        if type_type.compare(&cmp_type_type, ctx)? {
            Ok(())
        } else {
            let type_str = param.type_expr.print(ctx);
            let type_type_str = type_type.print(ctx);
            let cmp_type_type_str = cmp_type_type.print(ctx);
            Err(anyhow!("parameter type «{type_str} : {type_type_str}» must have type «{cmp_type_type_str}» instead"))
        }
    }
}

pub trait ExprManipulator {
    fn expr(&self, _expr: &mut Expr, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn param(&self, _param: &mut Param, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }

    fn params(&self, params: &mut [Param], ctx: &MetaLogicContext) -> Result<()> {
        for param_idx in 0..params.len() {
            let (prev, next) = params.split_at_mut(param_idx);
            let param = &mut next[0];
            ctx.with_locals(prev, |param_ctx| self.param(param, param_ctx))?;
        }
        Ok(())
    }

    fn arg(&self, _arg: &mut Arg, _ctx: &MetaLogicContext) -> Result<()> {
        Ok(())
    }
}

pub struct ImplicitArgInserter {
    pub max_depth: u32,
}

impl ImplicitArgInserter {
    pub fn insert_implicit_args_and_get_type(
        &self,
        expr: &mut Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        let mut expr_type = self.insert_implicit_args(expr, ctx)?;
        if self.max_depth > 0 && expr_type != Expr::Placeholder {
            let type_arg_inserter = ImplicitArgInserter {
                max_depth: self.max_depth - 1,
            };
            type_arg_inserter.insert_implicit_args(&mut expr_type, ctx)?;
            return Ok(expr_type);
        }
        Ok(Expr::Placeholder)
    }

    pub fn insert_implicit_args(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<Expr> {
        match expr {
            Expr::Placeholder => Ok(Expr::Placeholder),
            Expr::Var(var) => Ok(var.get_type(ctx)),
            Expr::App(app) => {
                let fun = &mut app.body;
                let arg = &mut app.param;
                let mut fun_type = self.insert_implicit_args_and_get_type(fun, ctx)?;
                self.arg(arg, ctx)?;
                while let Some(lambda) =
                    fun_type.match_generic_dep_type(DependentTypeCtorKind::Pi, true, ctx)
                {
                    if lambda.param.implicit && !arg.implicit {
                        *fun = Expr::app(
                            take(fun),
                            Arg {
                                expr: Expr::Placeholder,
                                implicit: true,
                            },
                        );
                        fun_type = lambda.apply(arg.clone(), ctx);
                    } else if arg.implicit && !lambda.param.implicit {
                        let name = lambda.param.get_name_or_placeholder();
                        return Err(anyhow!("expected explicit argument for «{name}»"));
                    } else {
                        return Ok(lambda.apply(arg.clone(), ctx));
                    }
                }
                return Ok(Expr::Placeholder);
            }
            Expr::Lambda(lambda) => {
                self.param(&mut lambda.param, ctx)?;
                ctx.with_local(&lambda.param, |body_ctx| {
                    let body_type =
                        self.insert_implicit_args_and_get_type(&mut lambda.body, body_ctx)?;
                    Expr::get_fun_type(&lambda.param, body_type, ctx)
                })
            }
        }
    }
}

impl ExprManipulator for ImplicitArgInserter {
    fn expr(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<()> {
        self.insert_implicit_args(expr, ctx)?;
        Ok(())
    }

    fn param(&self, param: &mut Param, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&mut param.type_expr, ctx)
    }

    fn arg(&self, arg: &mut Arg, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&mut arg.expr, ctx)
    }
}

pub struct PlaceholderFiller {
    pub force: bool,
    pub max_reduction_depth: u32,
}

impl PlaceholderFiller {
    pub fn try_fill_placeholders(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<Expr> {
        if self.force {
            let weak_filler = PlaceholderFiller {
                force: false,
                ..*self
            };
            weak_filler.fill_placeholders(expr, Expr::Placeholder, ctx)
        } else {
            self.fill_placeholders(expr, Expr::Placeholder, ctx)
        }
    }

    pub fn fill_placeholders(
        &self,
        expr: &mut Expr,
        mut expected_type: Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        self.fill_arg_placeholders(expr, &mut expected_type, ctx)?;
        self.fill_inner_placeholders(expr, expected_type, ctx)
    }

    fn fill_inner_placeholders(
        &self,
        expr: &mut Expr,
        mut expected_type: Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        match expr {
            Expr::Placeholder => {
                if self.force {
                    let type_str_options = MetaLogicContextOptions {
                        reduce_with_combinators: true,
                        print_all_implicit_args: false,
                    };
                    ctx.with_new_options(type_str_options, |type_str_ctx| {
                        let type_str = expected_type.print(type_str_ctx);
                        if let Ok(true) = expected_type.reduce(type_str_ctx, -1) {
                            let reduced_type_str = expected_type.print(type_str_ctx);
                            if reduced_type_str != type_str {
                                return Err(anyhow!("unfilled placeholder of type «{type_str}» (reduced: «{reduced_type_str}»)"));
                            }
                        }
                        Err(anyhow!("unfilled placeholder of type «{type_str}»"))
                    })
                } else {
                    Ok(Expr::Placeholder)
                }
            }
            Expr::Var(var) => Ok(var.get_type(ctx)),
            Expr::App(app) => {
                let fun = &mut app.body;
                let arg = &mut app.param;

                let initial_arg_type = self.try_fill_placeholders(&mut arg.expr, ctx)?;
                let initial_fun_type =
                    self.fill_arg_placeholders_in_fun(fun, arg, initial_arg_type, ctx)?;

                let fun_type_result =
                    self.fill_inner_placeholders(fun, initial_fun_type.clone(), ctx);
                // Report errors in arguments first, to better support the "underscore trick".
                let (mut fun_type, fun_type_err) = match fun_type_result {
                    Ok(fun_type) => (fun_type, Ok(())),
                    Err(err) => (self.try_fill_placeholders(fun, ctx)?, Err(err)),
                };
                //dbg!(
                //    "start",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    expected_type.print(ctx),
                //    initial_fun_type.print(ctx)
                //);
                let lambda = self.get_fun_type_lambda(&mut fun_type, arg.implicit, ctx)?;
                //dbg!(
                //    "fill arg placeholders",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    fun_type.print(ctx),
                //    lambda.param.type_expr.print(ctx)
                //);
                self.fill_placeholders(&mut arg.expr, lambda.param.type_expr.clone(), ctx)?;
                //dbg!(
                //    "filled arg placeholders",
                //    fun.print(ctx),
                //    arg.expr.print(ctx),
                //    fun_type.print(ctx),
                //    arg_type.print(ctx),
                //);
                fun_type_err?;
                Ok(lambda.apply(arg.clone(), ctx))
            }
            Expr::Lambda(lambda) => {
                let expected_type_lambda =
                    self.get_fun_type_lambda(&mut expected_type, lambda.param.implicit, ctx)?;
                if lambda.param.type_expr.is_empty() {
                    lambda.param.type_expr = expected_type_lambda.param.type_expr;
                }
                self.param(&mut lambda.param, ctx)?;
                ctx.with_local(&lambda.param, |body_ctx| {
                    let body_type = self.fill_placeholders(
                        &mut lambda.body,
                        expected_type_lambda.body,
                        body_ctx,
                    )?;
                    Expr::get_fun_type(&lambda.param, body_type, ctx)
                })
            }
        }
    }

    fn fill_arg_placeholders(
        &self,
        expr: &mut Expr,
        expected_type: &mut Expr,
        ctx: &MetaLogicContext,
    ) -> Result<bool> {
        if expected_type.is_empty() || !matches!(expr, Expr::App(_)) {
            return Ok(true);
        }

        let mut params = SmallVec::new();
        let mut args = SmallVec::new();
        let mut has_unfilled_args = false;
        let innermost_fun_type =
            self.analyze_app(expr, ctx, &mut params, &mut args, &mut has_unfilled_args)?;

        if has_unfilled_args {
            if ctx.with_locals(&params, |ctx_with_params| {
                //dbg!(
                //    "apply",
                //    fun.print(ctx),
                //    innermost_fun_type.print(ctx_with_params),
                //    expected_fun_type.print(ctx)
                //);
                innermost_fun_type.substitute_and_compare(
                    ctx_with_params,
                    &mut args,
                    expected_type,
                    ctx,
                )
            })? {
                Self::apply_args(expr, args);
                //dbg!("applied", fun.print(ctx));
            } else {
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn fill_arg_placeholders_in_fun(
        &self,
        fun: &mut Expr,
        arg: &mut Arg,
        initial_arg_type: Expr,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        let has_arg_type = !initial_arg_type.is_empty();
        let mut initial_fun_type =
            Self::get_expected_fun_type(initial_arg_type, arg.implicit, ctx)?;

        if has_arg_type {
            if !self.fill_arg_placeholders(fun, &mut initial_fun_type, ctx)? {
                //dbg!(
                //    "compare fail",
                //    fun.print(ctx),
                //    fun_params
                //        .iter()
                //        .map(|param| param.get_name_or_placeholder())
                //        .collect::<Vec<&str>>(),
                //    ctx.with_locals(&fun_params, |ctx_with_params| innermost_fun_type
                //        .print(ctx_with_params)),
                //    expected_fun_type.print(ctx)
                //);
                if self.max_reduction_depth > 0 {
                    //dbg!("reduce");
                    let mut initial_arg_type = self.try_fill_placeholders(&mut arg.expr, ctx)?;
                    if initial_arg_type.apply_one_reduction_rule(ctx)? {
                        //dbg!(initial_arg_type.print(ctx));
                        let sub_filler = PlaceholderFiller {
                            max_reduction_depth: self.max_reduction_depth - 1,
                            ..*self
                        };
                        initial_fun_type = sub_filler.fill_arg_placeholders_in_fun(
                            fun,
                            arg,
                            initial_arg_type,
                            ctx,
                        )?;
                        //dbg!("result", fun.print(ctx), arg.expr.print(ctx));
                    }
                }
            }
        }

        Ok(initial_fun_type)
    }

    fn get_expected_fun_type(
        initial_arg_type: Expr,
        implicit: bool,
        ctx: &MetaLogicContext,
    ) -> Result<Expr> {
        let expected_param = Param {
            name: None,
            type_expr: initial_arg_type.clone(),
            implicit,
        };
        ctx.lambda_handler().get_dep_type(
            initial_arg_type,
            Expr::lambda(expected_param, Expr::Placeholder),
            DependentTypeCtorKind::Pi,
            ctx.as_minimal(),
        )
    }

    /// Decomposes the type of the innermost function within `expr` (i.e. of the expression returned
    /// by `get_app_info`) into a telescope along with a body type in the context of that telescope.
    /// Also copies the corresponding argument expressions into `result_args`.
    /// Example: If we have `f : A → B → C`, then `analyze_app` of `f a b` yields `C` along with
    /// `result_params` of types `A` and `B`, and `result_args` `a` and `b`.
    fn analyze_app(
        &self,
        expr: &mut Expr,
        ctx: &MetaLogicContext,
        result_params: &mut SmallVec<[Param; INLINE_PARAMS]>,
        result_args: &mut SmallVec<[Expr; INLINE_PARAMS]>,
        has_unfilled_args: &mut bool,
    ) -> Result<Expr> {
        if let Expr::App(app) = expr {
            let fun = &mut app.body;
            let arg = &mut app.param;
            if arg.expr.is_empty() {
                *has_unfilled_args = true;
            }
            let mut fun_type =
                self.analyze_app(fun, ctx, result_params, result_args, has_unfilled_args)?;
            let lambda = ctx.with_locals(result_params, |fun_type_ctx| {
                self.get_fun_type_lambda(&mut fun_type, arg.implicit, fun_type_ctx)
            })?;
            result_params.push(lambda.param);
            result_args.push(arg.expr.clone());
            Ok(lambda.body)
        } else if *has_unfilled_args {
            self.try_fill_placeholders(expr, ctx)
        } else {
            // Skip unnecessary work if we don't have any arguments to fill.
            Ok(Expr::Placeholder)
        }
    }

    fn apply_args(mut expr: &mut Expr, mut args: SmallVec<[Expr; INLINE_PARAMS]>) {
        while let Expr::App(app) = expr {
            if let Some(value) = args.pop() {
                app.param.expr = value;
                expr = &mut app.body;
            } else {
                break;
            }
        }
    }

    fn get_fun_type_lambda(
        &self,
        fun_type: &mut Expr,
        implicit: bool,
        ctx: &MetaLogicContext,
    ) -> Result<LambdaExpr> {
        if let Some(lambda) = fun_type.match_generic_dep_type(DependentTypeCtorKind::Pi, true, ctx)
        {
            Ok(lambda)
        } else {
            //dbg!(fun_type.print(ctx));
            if self.max_reduction_depth > 0 && fun_type.apply_one_reduction_rule(ctx)? {
                //dbg!(fun_type.print(ctx));
                let sub_filler = PlaceholderFiller {
                    max_reduction_depth: self.max_reduction_depth - 1,
                    ..*self
                };
                return sub_filler.get_fun_type_lambda(fun_type, implicit, ctx);
            }

            Ok(LambdaExpr {
                param: Param {
                    name: None,
                    type_expr: Expr::Placeholder,
                    implicit,
                },
                body: Expr::Placeholder,
            })
        }
    }
}

impl ExprManipulator for PlaceholderFiller {
    fn expr(&self, expr: &mut Expr, ctx: &MetaLogicContext) -> Result<()> {
        self.fill_placeholders(expr, Expr::Placeholder, ctx)?;
        Ok(())
    }

    fn param(&self, param: &mut Param, ctx: &MetaLogicContext) -> Result<()> {
        let expected_type = ctx.lambda_handler().get_universe_type()?;
        self.fill_placeholders(&mut param.type_expr, expected_type, ctx)?;
        Ok(())
    }

    fn arg(&self, arg: &mut Arg, ctx: &MetaLogicContext) -> Result<()> {
        self.expr(&mut arg.expr, ctx)
    }
}

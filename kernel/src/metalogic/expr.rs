use std::{
    fmt::{self, Debug},
    rc::Rc,
};

use smallvec::{smallvec, SmallVec};

use super::{metalogic::*, parse::*, print::*};

use crate::{
    generic::{context::*, context_object::*, expr::*},
    util::parser::*,
};

#[derive(Clone, PartialEq)]
pub enum Expr {
    Var(Var), // includes primitive constants
    App(Box<AppExpr>),
    Lambda(Box<LambdaExpr>),
}

pub type AppExpr = App<Expr, Expr>;
pub type LambdaExpr = Lambda<Param, Expr>;

impl Expr {
    pub fn var(idx: VarIndex) -> Self {
        Expr::Var(Var(idx))
    }

    pub fn app(fun: Expr, arg: Expr) -> Self {
        Expr::App(Box::new(App {
            param: fun,
            body: arg,
        }))
    }

    pub fn multi_app(mut fun: Expr, args: SmallVec<[Expr; INLINE_PARAMS]>) -> Self {
        for arg in args {
            fun = Self::app(fun, arg);
        }
        fun
    }

    pub fn apply(fun: Expr, arg: Expr, ctx: &impl Context) -> Self {
        if let Expr::Lambda(lambda) = fun {
            let mut expr = lambda.body;
            expr.substitute(&mut [arg], true, ctx);
            expr
        } else {
            Self::app(fun, arg)
        }
    }

    pub fn multi_apply(
        mut fun: Expr,
        args: SmallVec<[Expr; INLINE_PARAMS]>,
        ctx: &impl Context,
    ) -> Self {
        for arg in args {
            fun = Self::apply(fun, arg, ctx);
        }
        fun
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
        };
        ctx.with_local(&param, |body_ctx| body.shift_to_subcontext(ctx, body_ctx));
        Self::lambda(param, body)
    }

    pub fn parse(s: &str, ctx: &MetaLogicContext) -> Result<Self, String> {
        let mut parser_input = ParserInput(s);
        let mut parsing_context = ParsingContext {
            input: &mut parser_input,
            context: ctx,
        };
        parsing_context.parse_expr()
    }

    pub fn print(&self, ctx: &MetaLogicContext) -> String {
        let mut result = String::new();
        let mut printing_context = PrintingContext {
            output: &mut result,
            context: ctx,
        };
        printing_context
            .print_expr(&self, false, false, false, false)
            .unwrap();
        result
    }

    pub fn reduce(&mut self, ctx: &MetaLogicContext, convert_to_combinators: bool) -> bool {
        let mut reduced = false;

        loop {
            match self {
                Expr::Var(_) => {}
                Expr::App(app) => {
                    reduced |= app.param.reduce(ctx, convert_to_combinators);
                    reduced |= app.body.reduce(ctx, convert_to_combinators);
                }
                Expr::Lambda(lambda) => {
                    reduced |= lambda.param.type_expr.reduce(ctx, convert_to_combinators);
                    ctx.with_local(&lambda.param, |body_ctx| {
                        reduced |= lambda.body.reduce(&body_ctx, convert_to_combinators);
                    });
                }
            }

            if let Some(red) = self.reduce_head(ctx) {
                *self = red;
                reduced = true;
            } else {
                return reduced;
            }
        }
    }

    fn reduce_head(&self, ctx: &MetaLogicContext) -> Option<Expr> {
        let mut expr = self.reduce_head_once(ctx)?;
        while let Some(expr_red) = expr.reduce_head_once(ctx) {
            expr = expr_red
        }
        Some(expr)
    }

    fn reduce_head_once(&self, ctx: &MetaLogicContext) -> Option<Expr> {
        if let Expr::App(app) = self {
            let mut fun = &app.param;
            let fun_red_opt = fun.reduce_head(ctx);
            if let Some(fun_red) = &fun_red_opt {
                fun = fun_red;
            }
            if let Expr::Lambda(lambda) = fun {
                let mut expr = lambda.body.clone();
                let arg = app.body.clone();
                expr.substitute(&mut [arg], true, ctx);
                return Some(expr);
            }
        }

        let red_ctx = ctx.as_minimal();
        for rule in &ctx.globals.reduction_rules {
            if let Some(mut args) = self.match_expr(&rule.params, &rule.body.source, &red_ctx) {
                let mut expr = rule.body.target.clone();
                expr.substitute(&mut args, true, &red_ctx);
                return Some(expr);
            }
        }

        None
    }

    pub fn match_expr<Ctx: ComparisonContext>(
        &self,
        match_params: &[Param],
        match_expr: &Expr,
        subst_ctx: &Ctx,
    ) -> Option<SmallVec<[Expr; INLINE_PARAMS]>> {
        let params_len = match_params.len();
        let mut args: SmallVec<[Expr; INLINE_PARAMS]> = smallvec![Expr::default(); params_len];
        let mut args_filled: SmallVec<[bool; INLINE_PARAMS]> = smallvec![false; params_len];
        if subst_ctx.with_locals(match_params, |ctx| {
            match_expr.substitute_and_compare(ctx, &mut args, &mut args_filled, self, subst_ctx)
        }) {
            if args_filled.iter().all(|filled| *filled) {
                return Some(args);
            }
        }
        None
    }

    pub fn get_type(&self, ctx: &MetaLogicContext) -> Result<Expr, String> {
        match self {
            Expr::Var(Var(idx)) => Ok(ctx.get_var(*idx).type_expr.shifted_from_var(ctx, *idx)),
            Expr::App(app) => {
                // Finding the result type of an application is surprisingly tricky because the
                // application itself does not include the type parameters of its function. Instead,
                // to determine the property we need to match the type of the actual function
                // argument against a term that denotes a sufficiently generic pi type. Then we
                // apply the property to the argument of the application.
                let fun = &app.param;
                let arg = &app.body;
                let fun_type = fun.get_type(ctx)?;
                let arg_type = arg.get_type(ctx)?;
                let (prop_param, cmp_fun_type) =
                    ctx.globals.lambda_handler.get_semi_generic_dep_type(
                        arg_type,
                        DependentTypeCtorKind::Pi,
                        ctx.as_minimal(),
                    )?;
                if let Some(mut prop_vec) = fun_type.match_expr(&[prop_param], &cmp_fun_type, ctx) {
                    let prop = prop_vec.pop().unwrap();
                    Ok(Expr::apply(prop, arg.clone(), ctx))
                } else {
                    let fun_str = fun.print(ctx);
                    let fun_type_str = fun_type.print(ctx);
                    let arg_str = arg.print(ctx);
                    let arg_type = arg.get_type(ctx)?;
                    let arg_type_str = arg_type.print(ctx);
                    Err(format!("application type mismatch: {fun_str} : {fun_type_str} cannot be applied to {arg_str} : {arg_type_str}"))
                }
            }
            Expr::Lambda(lambda) => {
                let body_type =
                    ctx.with_local(&lambda.param, |body_ctx| lambda.body.get_type(body_ctx))?;
                let body_type_lambda = Expr::lambda(lambda.param.clone(), body_type);
                ctx.globals.lambda_handler.get_dep_type(
                    lambda.param.type_expr.clone(),
                    body_type_lambda,
                    DependentTypeCtorKind::Pi,
                    ctx.as_minimal(),
                )
            }
        }
    }

    fn shift_and_compare_impl_no_red<Ctx: ComparisonContext>(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> bool {
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
            _ => false,
        }
    }

    fn substitute_and_compare_impl_no_red<Ctx: ComparisonContext>(
        &self,
        ctx: &Ctx,
        args: &mut [Expr],
        args_filled: &mut [bool],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> bool {
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
            _ => false,
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
    ) -> bool {
        if self.shift_and_compare_impl_no_red(ctx, orig_ctx, target, target_subctx) {
            return true;
        }

        if let Some(metalogic_ctx) = ctx.as_opt_metalogic_context() {
            if let Some(target_metalogic_ctx) = target_subctx.as_opt_metalogic_context() {
                let self_red_opt = self.reduce_head(metalogic_ctx);
                let target_red_opt = target.reduce_head(target_metalogic_ctx);
                if self_red_opt.is_some() || target_red_opt.is_some() {
                    let self_red = self_red_opt.as_ref().unwrap_or(self);
                    let target_red = target_red_opt.as_ref().unwrap_or(target);
                    if self_red.shift_and_compare_impl_no_red(
                        ctx,
                        orig_ctx,
                        target_red,
                        target_subctx,
                    ) {
                        return true;
                    }
                }
            }
        }

        false
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
    ) -> bool {
        if self.substitute_and_compare_impl_no_red(
            ctx,
            args,
            args_filled,
            subst_ctx,
            target,
            target_subctx,
        ) {
            return true;
        }

        if let Some(metalogic_ctx) = ctx.as_opt_metalogic_context() {
            if let Some(target_metalogic_ctx) = target_subctx.as_opt_metalogic_context() {
                let self_red_opt = self.reduce_head(metalogic_ctx);
                let target_red_opt = target.reduce_head(target_metalogic_ctx);
                if self_red_opt.is_some() || target_red_opt.is_some() {
                    let self_red = self_red_opt.as_ref().unwrap_or(self);
                    let target_red = target_red_opt.as_ref().unwrap_or(target);
                    if self_red.substitute_and_compare_impl_no_red(
                        ctx,
                        args,
                        args_filled,
                        subst_ctx,
                        target_red,
                        target_subctx,
                    ) {
                        return true;
                    }
                }
            }
        }

        false
    }
}

#[derive(Clone, Default)]
pub struct Param {
    pub name: Option<Rc<String>>,
    pub type_expr: Expr,
}

impl Param {
    pub fn print_name(&self, f: &mut impl fmt::Write) -> fmt::Result {
        let param_name = if let Some(name) = &self.name {
            name
        } else {
            "_"
        };
        f.write_str(param_name)
    }
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
        self.print_name(f)?;
        f.write_str(":")?;
        self.type_expr.fmt(f)
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
    ) -> bool {
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
    ) -> bool {
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

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
    fn shift_vars(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        match self {
            Expr::Var(var) => var.shift_vars(start, end, shift),
            Expr::App(app) => app.shift_vars(start, end, shift),
            Expr::Lambda(lambda) => lambda.shift_vars(start, end, shift),
        }
    }

    fn with_shifted_vars(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        match self {
            Expr::Var(var) => Expr::Var(var.with_shifted_vars(start, end, shift)),
            Expr::App(app) => Expr::App(Box::new(app.with_shifted_vars(start, end, shift))),
            Expr::Lambda(lambda) => {
                Expr::Lambda(Box::new(lambda.with_shifted_vars(start, end, shift)))
            }
        }
    }

    fn count_refs(&self, start: VarIndex, ref_counts: &mut [usize]) {
        match self {
            Expr::Var(var) => var.count_refs(start, ref_counts),
            Expr::App(app) => app.count_refs(start, ref_counts),
            Expr::Lambda(lambda) => lambda.count_refs(start, ref_counts),
        }
    }

    fn has_refs(&self, start: VarIndex, end: VarIndex) -> bool {
        match self {
            Expr::Var(var) => var.has_refs(start, end),
            Expr::App(app) => app.has_refs(start, end),
            Expr::Lambda(lambda) => lambda.has_refs(start, end),
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
                    var.get_subst_arg(shift_start, args_start, args, ref_counts)
                {
                    *self = subst_arg;
                } else {
                    var.shift_vars(shift_start, args_start, args.len() as VarIndex);
                }
            }
            Expr::App(app) => app.substitute_impl(shift_start, args_start, args, ref_counts),
            Expr::Lambda(lambda) => {
                lambda.substitute_impl(shift_start, args_start, args, ref_counts)
            }
        }
    }
}

impl ContextObjectWithCmp<Option<&MetaLogic>> for Expr {
    fn shift_and_compare(
        &self,
        start: VarIndex,
        end: VarIndex,
        shift: VarIndex,
        target: &Self,
        cmp_data: &Option<&MetaLogic>,
    ) -> bool {
        if self.shift_and_compare_impl(start, end, shift, target, cmp_data) {
            return true;
        }

        if let Some(metalogic) = cmp_data {
            let self_red_opt = self.reduce_head(metalogic, start);
            let target_start = start - end;
            let target_red_opt = target.reduce_head(metalogic, target_start);
            if self_red_opt.is_some() || target_red_opt.is_some() {
                let self_red = self_red_opt.as_ref().unwrap_or(self);
                let target_red = target_red_opt.as_ref().unwrap_or(target);
                if self_red.shift_and_compare_impl(start, end, shift, target_red, cmp_data) {
                    return true;
                }
            }
        }

        false
    }
}

impl ContextObjectWithSubstCmp<Expr, Option<&MetaLogic>> for Expr {
    fn substitute_and_compare(
        &self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [Expr],
        args_filled: &mut [bool],
        target: &Self,
        cmp_data: &Option<&MetaLogic>,
    ) -> bool {
        if self.substitute_and_compare_impl(
            shift_start,
            args_start,
            args,
            args_filled,
            target,
            cmp_data,
        ) {
            return true;
        }

        if let Some(metalogic) = cmp_data {
            let self_red_opt = self.reduce_head(metalogic, shift_start);
            let args_end = args_start + args.len() as VarIndex;
            let target_shift_start = shift_start - args_end;
            let target_red_opt = target.reduce_head(metalogic, target_shift_start);
            if self_red_opt.is_some() || target_red_opt.is_some() {
                let self_red = self_red_opt.as_ref().unwrap_or(self);
                let target_red = target_red_opt.as_ref().unwrap_or(target);
                if self_red.substitute_and_compare_impl(
                    shift_start,
                    args_start,
                    args,
                    args_filled,
                    target_red,
                    cmp_data,
                ) {
                    return true;
                }
            }
        }

        false
    }
}

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

    pub fn apply(fun: Expr, arg: Expr, locals_start: VarIndex) -> Self {
        if let Expr::Lambda(lambda) = fun {
            let mut expr = lambda.body;
            expr.substitute(locals_start - 1, -1, &mut [arg], true);
            expr
        } else {
            Self::app(fun, arg)
        }
    }

    pub fn multi_apply(
        mut fun: Expr,
        args: SmallVec<[Expr; INLINE_PARAMS]>,
        locals_start: VarIndex,
    ) -> Self {
        for arg in args {
            fun = Self::apply(fun, arg, locals_start);
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

    pub fn const_lambda(domain: Expr, mut body: Expr, locals_start: VarIndex) -> Self {
        let param = Param {
            name: None,
            type_expr: domain,
        };
        body.shift_vars(locals_start, 0, -1);
        Self::lambda(param, body)
    }

    pub fn parse(
        s: &str,
        ctx: &Context<Param>,
        lambda_handler: &dyn LambdaHandler,
    ) -> Result<Self, String> {
        let mut parser_input = ParserInput(s);
        let mut parsing_context = ParsingContext {
            input: &mut parser_input,
            context: ctx,
            lambda_handler,
        };
        parsing_context.parse_expr()
    }

    pub fn print(&self, ctx: &Context<Param>, lambda_handler: &dyn LambdaHandler) -> String {
        let mut result = String::new();
        let mut printing_context = PrintingContext {
            output: &mut result,
            context: ctx,
            lambda_handler,
        };
        printing_context
            .print_expr(&self, false, false, false, false)
            .unwrap();
        result
    }

    pub fn reduce(
        &mut self,
        metalogic: &MetaLogic,
        locals_start: VarIndex,
        convert_to_combinators: bool,
    ) -> bool {
        let mut reduced = false;

        loop {
            match self {
                Expr::Var(_) => {}
                Expr::App(app) => {
                    reduced |= app
                        .param
                        .reduce(metalogic, locals_start, convert_to_combinators);
                    reduced |= app
                        .body
                        .reduce(metalogic, locals_start, convert_to_combinators);
                }
                Expr::Lambda(lambda) => {
                    reduced |= lambda.param.type_expr.reduce(
                        metalogic,
                        locals_start,
                        convert_to_combinators,
                    );
                    reduced |=
                        lambda
                            .body
                            .reduce(metalogic, locals_start - 1, convert_to_combinators);
                }
            }

            if let Some(red) = self.reduce_head(metalogic, locals_start) {
                *self = red;
                reduced = true;
            } else {
                return reduced;
            }
        }
    }

    fn reduce_head(&self, metalogic: &MetaLogic, locals_start: VarIndex) -> Option<Expr> {
        let mut expr = self.reduce_head_once(metalogic, locals_start)?;
        while let Some(expr_red) = expr.reduce_head_once(metalogic, locals_start) {
            expr = expr_red
        }
        Some(expr)
    }

    fn reduce_head_once(&self, metalogic: &MetaLogic, locals_start: VarIndex) -> Option<Expr> {
        if let Expr::App(app) = self {
            let mut fun = &app.param;
            let fun_red_opt = fun.reduce_head(metalogic, locals_start);
            if let Some(fun_red) = &fun_red_opt {
                fun = fun_red;
            }
            if let Expr::Lambda(lambda) = fun {
                let mut expr = lambda.body.clone();
                let arg = app.body.clone();
                expr.substitute(locals_start - 1, -1, &mut [arg], true);
                return Some(expr);
            }
        }

        for rule in metalogic.get_reduction_rules() {
            if let Some(mut args) =
                self.match_expr(&None, &rule.params, &rule.body.source, locals_start)
            {
                let mut expr = rule.body.target.clone();
                let args_start = -(args.len() as VarIndex);
                expr.substitute(locals_start + args_start, args_start, &mut args, true);
                return Some(expr);
            }
        }

        None
    }

    pub fn match_expr(
        &self,
        cmp_data: &Option<&MetaLogic>,
        match_params: &[Param],
        match_expr: &Expr,
        locals_start: VarIndex,
    ) -> Option<SmallVec<[Expr; INLINE_PARAMS]>> {
        let params_len = match_params.len();
        let args_start = -(params_len as VarIndex);
        let mut args: SmallVec<[Expr; INLINE_PARAMS]> = smallvec![Expr::default(); params_len];
        let mut args_filled: SmallVec<[bool; INLINE_PARAMS]> = smallvec![false; params_len];
        if match_expr.substitute_and_compare(
            locals_start + args_start,
            args_start,
            &mut args,
            &mut args_filled,
            self,
            cmp_data,
        ) {
            if args_filled.iter().all(|filled| *filled) {
                return Some(args);
            }
        }
        None
    }

    fn shift_and_compare_impl(
        &self,
        start: VarIndex,
        end: VarIndex,
        shift: VarIndex,
        target: &Self,
        cmp_data: &Option<&MetaLogic>,
    ) -> bool {
        match (self, target) {
            (Expr::Var(var), Expr::Var(target_var)) => {
                var.shift_and_compare(start, end, shift, target_var, cmp_data)
            }
            (Expr::App(app), Expr::App(target_app)) => {
                app.shift_and_compare(start, end, shift, target_app, cmp_data)
            }
            (Expr::Lambda(lambda), Expr::Lambda(target_lambda)) => {
                lambda.shift_and_compare(start, end, shift, target_lambda, cmp_data)
            }
            _ => false,
        }
    }

    fn substitute_and_compare_impl(
        &self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [Expr],
        args_filled: &mut [bool],
        target: &Self,
        cmp_data: &Option<&MetaLogic>,
    ) -> bool {
        if let Expr::Var(var) = self {
            if let Some(result) =
                var.compare_subst_arg(shift_start, args_start, args, args_filled, target, cmp_data)
            {
                return result;
            }
        }

        match (self, target) {
            (Expr::Var(var), Expr::Var(target_var)) => var.shift_and_compare(
                shift_start,
                args_start,
                args.len() as VarIndex,
                target_var,
                cmp_data,
            ),
            (Expr::App(app), Expr::App(target_app)) => app.substitute_and_compare(
                shift_start,
                args_start,
                args,
                args_filled,
                target_app,
                cmp_data,
            ),
            (Expr::Lambda(lambda), Expr::Lambda(target_lambda)) => lambda.substitute_and_compare(
                shift_start,
                args_start,
                args,
                args_filled,
                target_lambda,
                cmp_data,
            ),
            _ => false,
        }
    }
}

#[derive(Clone, Default)]
pub struct Param {
    pub name: Option<Rc<String>>,
    pub type_expr: Expr,
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
    fn shift_vars(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        self.type_expr.shift_vars(start, end, shift);
    }

    fn with_shifted_vars(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        Param {
            name: self.name.clone(),
            type_expr: self.type_expr.with_shifted_vars(start, end, shift),
        }
    }

    fn count_refs(&self, start: VarIndex, ref_counts: &mut [usize]) {
        self.type_expr.count_refs(start, ref_counts);
    }

    fn has_refs(&self, start: VarIndex, end: VarIndex) -> bool {
        self.type_expr.has_refs(start, end)
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

impl ContextObjectWithCmp<Option<&MetaLogic>> for Param {
    fn shift_and_compare(
        &self,
        start: VarIndex,
        end: VarIndex,
        shift: VarIndex,
        target: &Self,
        cmp_data: &Option<&MetaLogic>,
    ) -> bool {
        self.type_expr
            .shift_and_compare(start, end, shift, &target.type_expr, cmp_data)
    }
}

impl ContextObjectWithSubstCmp<Expr, Option<&MetaLogic>> for Param {
    fn substitute_and_compare(
        &self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [Expr],
        args_filled: &mut [bool],
        target: &Self,
        cmp_data: &Option<&MetaLogic>,
    ) -> bool {
        self.type_expr.substitute_and_compare(
            shift_start,
            args_start,
            args,
            args_filled,
            &target.type_expr,
            cmp_data,
        )
    }
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

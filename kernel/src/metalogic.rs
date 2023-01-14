use std::{
    fmt::{self, Debug},
    rc::Rc,
};

use smallvec::{smallvec, SmallVec};

use crate::{context::*, context_object::*, expr::*, util::parser::*};

pub struct MetaLogic {
    constants: Vec<Param>,
    reduction_rules: Vec<ReductionRule>,
    lambda_handler: Box<dyn LambdaHandler>,
}

pub type ParamInit<'a> = (&'a str, &'a str);
pub type ReductionRuleInit<'a> = (&'a [ParamInit<'a>], &'a str, &'a str);

impl MetaLogic {
    pub fn construct<F>(
        constants_init: &[ParamInit],
        reduction_rules_init: &[ReductionRuleInit],
        create_lambda_handler: F,
    ) -> Result<Self, String>
    where
        F: FnOnce(&Context<Param>) -> Box<dyn LambdaHandler>,
    {
        let mut constants: Vec<Param> = constants_init
            .iter()
            .map(|(name, _)| Param {
                name: Some(Rc::new((*name).into())),
                type_expr: Expr::default(),
            })
            .collect();

        let lambda_handler = create_lambda_handler(&Context::new(&constants));

        let mut idx = 0;
        for (_, type_str) in constants_init {
            let ctx = Context::new(&constants);
            constants[idx].type_expr = Expr::parse(type_str, &ctx, lambda_handler.as_ref())?;
            idx += 1;
        }

        let root_ctx = Context::new(&constants);

        let reduction_rules: Result<Vec<ReductionRule>, String> = reduction_rules_init
            .iter()
            .map(|(params_init, source_init, target_init)| {
                let mut params = SmallVec::with_capacity(params_init.len());
                for (name, type_str) in params_init.iter() {
                    let ctx = root_ctx.with_locals(&params);
                    params.push(Param {
                        name: Some(Rc::new((*name).into())),
                        type_expr: Expr::parse(type_str, &ctx, lambda_handler.as_ref())?,
                    })
                }
                let ctx = root_ctx.with_locals(&params);
                let source = Expr::parse(source_init, &ctx, lambda_handler.as_ref())?;
                let target = Expr::parse(target_init, &ctx, lambda_handler.as_ref())?;
                Ok(ReductionRule {
                    params,
                    body: ReductionBody { source, target },
                })
            })
            .collect();

        Ok(MetaLogic {
            constants,
            reduction_rules: reduction_rules?,
            lambda_handler,
        })
    }

    pub fn get_root_context(&self) -> Context<Param> {
        Context::new(&self.constants)
    }

    pub fn get_constant(&self, name: &str) -> Option<&Param> {
        let ctx = self.get_root_context();
        let var_idx = ctx.get_var_index(name)?;
        Some(ctx.get_var(var_idx))
    }

    pub fn parse_expr(&self, s: &str, ctx: &Context<Param>) -> Result<Expr, String> {
        Expr::parse(s, ctx, self.lambda_handler.as_ref())
    }

    pub fn print_expr(&self, expr: &Expr, ctx: &Context<Param>) -> String {
        expr.print(ctx, self.lambda_handler.as_ref())
    }

    pub fn reduce_expr(
        &self,
        expr: &mut Expr,
        ctx: &Context<Param>,
        convert_to_combinators: bool,
    ) -> bool {
        expr.reduce(self, ctx.locals_start(), convert_to_combinators)
    }

    pub fn get_expr_type(&self, expr: &Expr, ctx: &Context<Param>) -> Result<Expr, String> {
        match expr {
            Expr::Var(Var(idx)) => Ok(ctx.shifted_to_context(&ctx.get_var(*idx).type_expr, *idx)),
            Expr::App(app) => {
                // Finding the result type of an application is surprisingly tricky because the
                // application itself does not include the type parameters of its function. Instead,
                // to determine the property we need to match the type of the actual function
                // argument against a term that denotes a sufficiently generic pi type. Then we
                // apply the property to the argument of the application.
                let fun = &app.param;
                let arg = &app.body;
                let fun_type = self.get_expr_type(fun, ctx)?;
                let arg_type = self.get_expr_type(arg, ctx)?;
                let locals_start = ctx.locals_start();
                let (prop_param, cmp_fun_type) = self.lambda_handler.get_semi_generic_dep_type(
                    arg_type,
                    DependentTypeCtorKind::Pi,
                    locals_start,
                )?;
                if let Some(mut prop_vec) =
                    fun_type.match_expr(&Some(self), &[prop_param], &cmp_fun_type, locals_start)
                {
                    let prop = prop_vec.pop().unwrap();
                    Ok(Expr::apply(prop, arg.clone(), locals_start))
                } else {
                    let fun_str = self.print_expr(fun, ctx);
                    let fun_type_str = self.print_expr(&fun_type, ctx);
                    let arg_str = self.print_expr(arg, ctx);
                    let arg_type = self.get_expr_type(arg, ctx)?;
                    let arg_type_str = self.print_expr(&arg_type, ctx);
                    Err(format!("application type mismatch: {fun_str} : {fun_type_str} cannot be applied to {arg_str} : {arg_type_str}"))
                }
            }
            Expr::Lambda(lambda) => {
                let body_ctx = ctx.with_local(&lambda.param);
                let body_type = self.get_expr_type(&lambda.body, &body_ctx)?;
                let body_type_lambda = Expr::lambda(lambda.param.clone(), body_type);
                self.lambda_handler.get_dep_type(
                    lambda.param.type_expr.clone(),
                    body_type_lambda,
                    DependentTypeCtorKind::Pi,
                    ctx.locals_start(),
                )
            }
        }
    }

    pub fn check_reduction_rule_types(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        let root_ctx = self.get_root_context();

        for rule in &self.reduction_rules {
            if let Err(error) = self.check_reduction_rule_type(rule, &root_ctx) {
                errors.push(error);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn check_reduction_rule_type(
        &self,
        rule: &ReductionRule,
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        let rule_ctx = ctx.with_locals(&rule.params);
        let source_type = self.get_expr_type(&rule.body.source, &rule_ctx)?;
        let target_type = self.get_expr_type(&rule.body.target, &rule_ctx)?;
        if source_type.compare(rule_ctx.locals_start(), &target_type, &Some(self)) {
            Ok(())
        } else {
            let source_str = self.print_expr(&rule.body.source, &rule_ctx);
            let source_type_str = self.print_expr(&source_type, &rule_ctx);
            let target_str = self.print_expr(&rule.body.target, &rule_ctx);
            let target_type_str = self.print_expr(&target_type, &rule_ctx);
            Err(format!("type conflict in reduction rule between {source_str} : {source_type_str} and {target_str} : {target_type_str}"))
        }
    }

    pub fn check_type_of_types(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        let root_ctx = self.get_root_context();

        for constant in &self.constants {
            if let Err(error) = self.check_type_of_types_in_param(constant, &root_ctx) {
                errors.push(error);
            }
        }

        for rule in &self.reduction_rules {
            if let Err(error) = self.check_type_of_types_in_reduction_rule(rule, &root_ctx) {
                errors.push(error);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn check_type_of_types_in_param(
        &self,
        param: &Param,
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        self.check_type_of_types_in_expr(&param.type_expr, ctx)?;
        let type_type = self.get_expr_type(&param.type_expr, ctx)?;
        let cmp_type_type = self.lambda_handler.get_universe_type()?;
        if type_type.compare(ctx.locals_start(), &cmp_type_type, &Some(self)) {
            Ok(())
        } else {
            let type_str = self.print_expr(&param.type_expr, &ctx);
            let type_type_str = self.print_expr(&type_type, &ctx);
            let cmp_type_type_str = self.print_expr(&cmp_type_type, &ctx);
            Err(format!("parameter type {type_str} : {type_type_str} must have type {cmp_type_type_str} instead"))
        }
    }

    fn check_type_of_types_in_params(
        &self,
        params: &[Param],
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        for param_idx in 0..params.len() {
            let param = &params[param_idx];
            let param_ctx = ctx.with_locals(&params[0..param_idx]);
            self.check_type_of_types_in_param(param, &param_ctx)?;
        }
        Ok(())
    }

    fn check_type_of_types_in_expr(&self, expr: &Expr, ctx: &Context<Param>) -> Result<(), String> {
        match expr {
            Expr::Var(_) => {}
            Expr::App(app) => {
                self.check_type_of_types_in_expr(&app.param, ctx)?;
                self.check_type_of_types_in_expr(&app.body, ctx)?;
            }
            Expr::Lambda(lambda) => {
                self.check_type_of_types_in_param(&lambda.param, ctx)?;
                let body_ctx = ctx.with_local(&lambda.param);
                self.check_type_of_types_in_expr(&lambda.body, &body_ctx)?;
            }
        };
        Ok(())
    }

    fn check_type_of_types_in_reduction_rule(
        &self,
        rule: &ReductionRule,
        ctx: &Context<Param>,
    ) -> Result<(), String> {
        self.check_type_of_types_in_params(&rule.params, ctx)?;
        let rule_ctx = ctx.with_locals(&rule.params);
        self.check_type_of_types_in_expr(&rule.body.source, &rule_ctx)?;
        self.check_type_of_types_in_expr(&rule.body.target, &rule_ctx)?;
        Ok(())
    }
}

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

    fn parse(
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
        parsing_context.parse()
    }

    fn print(&self, ctx: &Context<Param>, lambda_handler: &dyn LambdaHandler) -> String {
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

    fn reduce(
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

        for rule in metalogic.reduction_rules.iter() {
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

pub type ReductionRule = MultiLambda<Param, ReductionBody>;

pub struct ReductionBody {
    pub source: Expr,
    pub target: Expr,
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum DependentTypeCtorKind {
    Pi,
    Sigma,
}

pub trait LambdaHandler {
    fn get_universe_type(&self) -> Result<Expr, String>;

    fn get_dep_type(
        &self,
        domain: Expr,
        prop: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<Expr, String>;

    fn get_indep_type(
        &self,
        domain: Expr,
        codomain: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<Expr, String> {
        let prop = Expr::const_lambda(domain.clone(), codomain, locals_start);
        self.get_dep_type(domain, prop, kind, locals_start)
    }

    fn get_prop_type(&self, domain: Expr, locals_start: VarIndex) -> Result<Expr, String> {
        self.get_indep_type(
            domain,
            self.get_universe_type()?,
            DependentTypeCtorKind::Pi,
            locals_start,
        )
    }

    fn get_semi_generic_dep_type(
        &self,
        domain: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<(Param, Expr), String> {
        let domain_in_prop_var_ctx = domain.with_shifted_vars(locals_start, 0, -1);
        let prop_param = Param {
            name: None,
            type_expr: self.get_prop_type(domain, locals_start)?,
        };
        let prop_var = Expr::var(-1);
        let dep_type =
            self.get_dep_type(domain_in_prop_var_ctx, prop_var, kind, locals_start - 1)?;
        Ok((prop_param, dep_type))
    }

    fn get_generic_dep_type(
        &self,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<(Param, Param, Expr), String> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let domain_var = Expr::var(-1);
        let (prop_param, dep_type) =
            self.get_semi_generic_dep_type(domain_var, kind, locals_start - 1)?;
        Ok((domain_param, prop_param, dep_type))
    }

    fn get_generic_indep_type(
        &self,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<(Param, Param, Expr), String> {
        let domain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let codomain_param = Param {
            name: None,
            type_expr: self.get_universe_type()?,
        };
        let domain_var = Expr::var(-2);
        let codomain_var = Expr::var(-1);
        let indep_type = self.get_indep_type(domain_var, codomain_var, kind, locals_start - 2)?;
        Ok((domain_param, codomain_param, indep_type))
    }

    fn get_id_cmb(&self, domain: Expr, locals_start: VarIndex) -> Result<Expr, String>;

    fn get_const_cmb(
        &self,
        domain: Expr,
        codomain: Expr,
        locals_start: VarIndex,
    ) -> Result<Expr, String>;

    fn get_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        prop2: Expr,
        locals_start: VarIndex,
    ) -> Result<Expr, String>;
}

struct ParsingContext<'a, 'b, 'c, 'd: 'c> {
    input: &'a mut ParserInput<'b>,
    context: &'a Context<'c, 'd, 'a, Param>,
    lambda_handler: &'a dyn LambdaHandler,
}

impl<'a, 'b, 'c, 'd> ParsingContext<'a, 'b, 'c, 'd> {
    fn parse(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_prod()?;
        if self.input.try_read_char('→') {
            let codomain = self.parse()?;
            expr = self.lambda_handler.get_indep_type(
                expr,
                codomain,
                DependentTypeCtorKind::Pi,
                self.context.locals_start(),
            )?;
        }
        Ok(expr)
    }

    fn parse_prod(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_app()?;
        if self.input.try_read_char('×') {
            let right = self.parse_app()?;
            expr = self.lambda_handler.get_indep_type(
                expr,
                right,
                DependentTypeCtorKind::Sigma,
                self.context.locals_start(),
            )?;
        }
        Ok(expr)
    }

    fn parse_app(&mut self) -> Result<Expr, String> {
        self.input.skip_whitespace();
        if let Some(mut expr) = self.try_parse_one()? {
            self.input.skip_whitespace();
            while let Some(arg) = self.try_parse_one()? {
                expr = Expr::app(expr, arg);
                self.input.skip_whitespace();
            }
            Ok(expr)
        } else {
            self.input.expected("expression")
        }
    }

    fn try_parse_one(&mut self) -> Result<Option<Expr>, String> {
        if self.input.try_read_char('(') {
            let expr = self.parse()?;
            self.input.read_char(')')?;
            Ok(Some(expr))
        } else if self.input.try_read_char('λ') {
            let (params, body) = self.parse_lambda()?;
            Ok(Some(Expr::multi_lambda(params, body)))
        } else if self.input.try_read_char('Π') {
            let expr = self.parse_dep_type(DependentTypeCtorKind::Pi)?;
            Ok(Some(expr))
        } else if self.input.try_read_char('Σ') {
            let expr = self.parse_dep_type(DependentTypeCtorKind::Sigma)?;
            Ok(Some(expr))
        } else if let Some(name) = self.input.try_read_name() {
            if let Some(var_idx) = self.context.get_var_index(name) {
                Ok(Some(Expr::var(var_idx)))
            } else {
                let msg = format!("variable '{name}' not found");
                self.input.error(msg)
            }
        } else {
            Ok(None)
        }
    }

    fn parse_lambda(&mut self) -> Result<(SmallVec<[Param; INLINE_PARAMS]>, Expr), String> {
        self.input.skip_whitespace();
        if let Some(param_name_str) = self.input.try_read_name() {
            let mut param_names: SmallVec<[String; INLINE_PARAMS]> =
                smallvec![param_name_str.into()];
            self.input.skip_whitespace();
            while let Some(param_name_str) = self.input.try_read_name() {
                param_names.push(param_name_str.into());
                self.input.skip_whitespace();
            }
            self.input.read_char(':')?;
            let param_type = self.parse()?;
            self.input.read_char('.')?;
            let mut params: SmallVec<[Param; INLINE_PARAMS]> =
                SmallVec::with_capacity(param_names.len());
            let locals_start = self.context.locals_start();
            let mut shift: VarIndex = 0;
            for param_name in param_names {
                params.push(Param {
                    name: Some(Rc::new(param_name)),
                    type_expr: param_type.with_shifted_vars(locals_start, 0, shift),
                });
                shift -= 1;
            }
            let mut body_ctx = ParsingContext {
                input: self.input,
                context: &self.context.with_locals(&params),
                lambda_handler: self.lambda_handler,
            };
            let body = body_ctx.parse()?;
            Ok((params, body))
        } else {
            self.input.expected("identifier")
        }
    }

    fn parse_dep_type(&mut self, kind: DependentTypeCtorKind) -> Result<Expr, String> {
        let (mut params, body) = self.parse_lambda()?;
        self.create_multi_dep_type(&mut params, body, kind, self.context.locals_start())
    }

    fn create_multi_dep_type(
        &self,
        params: &mut [Param],
        body: Expr,
        kind: DependentTypeCtorKind,
        locals_start: VarIndex,
    ) -> Result<Expr, String> {
        if let Some((param, rest_params)) = params.split_first_mut() {
            let rest = self.create_multi_dep_type(rest_params, body, kind, locals_start - 1)?;
            let domain = param.type_expr.clone();
            let prop = Expr::lambda(std::mem::take(param), rest);
            self.lambda_handler
                .get_dep_type(domain, prop, kind, locals_start)
        } else {
            Ok(body)
        }
    }
}

struct PrintingContext<'a, 'b, 'c: 'b, W: fmt::Write> {
    output: &'a mut W,
    context: &'a Context<'b, 'c, 'a, Param>,
    lambda_handler: &'a dyn LambdaHandler,
}

impl<'a, 'b, 'c, W: fmt::Write> PrintingContext<'a, 'b, 'c, W> {
    fn print_expr(
        &mut self,
        expr: &Expr,
        parens_for_app: bool,
        parens_for_lambda: bool,
        parens_for_fun: bool,
        parens_for_prod: bool,
    ) -> fmt::Result {
        if self.try_print_special(
            expr,
            DependentTypeCtorKind::Pi,
            'Π',
            '→',
            parens_for_lambda,
            parens_for_fun,
        )? {
            return Ok(());
        }

        if self.try_print_special(
            expr,
            DependentTypeCtorKind::Sigma,
            'Σ',
            '×',
            parens_for_lambda,
            parens_for_prod,
        )? {
            return Ok(());
        }

        match expr {
            Expr::Var(Var(idx)) => self.context.get_var(*idx).print_name(self.output)?,
            Expr::App(app) => {
                if parens_for_app {
                    self.output.write_char('(')?;
                }
                self.print_expr(&app.param, false, true, true, true)?;
                self.output.write_char(' ')?;
                self.print_expr(&app.body, true, true, true, true)?;
                if parens_for_app {
                    self.output.write_char(')')?;
                }
            }
            Expr::Lambda(lambda) => {
                if parens_for_lambda {
                    self.output.write_char('(')?;
                }
                self.output.write_str("λ ")?;
                self.print_lambda(lambda)?;
                if parens_for_lambda {
                    self.output.write_char(')')?;
                }
            }
        }
        Ok(())
    }

    fn print_lambda(&mut self, lambda: &LambdaExpr) -> fmt::Result {
        self.print_param(&lambda.param)?;
        self.output.write_str(". ")?;
        let mut body_ctx = PrintingContext {
            output: self.output,
            context: &self.context.with_local(&lambda.param),
            lambda_handler: self.lambda_handler,
        };
        body_ctx.print_expr(&lambda.body, false, false, true, true)?;
        Ok(())
    }

    fn print_param(&mut self, param: &Param) -> fmt::Result {
        param.print_name(self.output)?;
        self.output.write_str(" : ")?;
        self.print_expr(&param.type_expr, false, true, false, false)?;
        Ok(())
    }

    fn try_print_special(
        &mut self,
        expr: &Expr,
        kind: DependentTypeCtorKind,
        prefix: char,
        infix: char,
        parens_for_prefix: bool,
        parens_for_infix: bool,
    ) -> Result<bool, fmt::Error> {
        let locals_start = self.context.locals_start();

        if let Ok((domain_param, codomain_param, generic_indep_type)) = self
            .lambda_handler
            .get_generic_indep_type(kind, locals_start)
        {
            if let Some(arg_vec) = expr.match_expr(
                &None,
                &[domain_param, codomain_param],
                &generic_indep_type,
                locals_start,
            ) {
                let domain = &arg_vec[0];
                let codomain = &arg_vec[1];
                if parens_for_infix {
                    self.output.write_char('(')?;
                }
                self.print_expr(&domain, false, true, true, true)?;
                self.output.write_char(' ')?;
                self.output.write_char(infix)?;
                self.output.write_char(' ')?;
                self.print_expr(
                    &codomain,
                    false,
                    true,
                    kind != DependentTypeCtorKind::Pi,
                    true,
                )?;
                if parens_for_infix {
                    self.output.write_char(')')?;
                }
                return Ok(true);
            }
        }

        if let Ok((domain_param, prop_param, generic_dep_type)) =
            self.lambda_handler.get_generic_dep_type(kind, locals_start)
        {
            if let Some(arg_vec) = expr.match_expr(
                &None,
                &[domain_param, prop_param],
                &generic_dep_type,
                locals_start,
            ) {
                if let Expr::Lambda(lambda) = &arg_vec[1] {
                    if parens_for_prefix {
                        self.output.write_char('(')?;
                    }
                    self.output.write_char(prefix)?;
                    self.output.write_char(' ')?;
                    self.print_lambda(lambda)?;
                    if parens_for_prefix {
                        self.output.write_char(')')?;
                    }
                    return Ok(true);
                }
            }
        }

        Ok(false)
    }
}

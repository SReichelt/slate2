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

type ParamInit<'a> = (&'a str, &'a str);
type ReductionRuleInit<'a> = (&'a [ParamInit<'a>], &'a str, &'a str);

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

        let mut idx = 0;
        for (_, type_str) in constants_init {
            constants[idx].type_expr = Expr::parse(type_str, &Context::new(&constants))?;
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
                        type_expr: Expr::parse(type_str, &ctx)?,
                    })
                }
                let ctx = root_ctx.with_locals(&params);
                let source = Expr::parse(source_init, &ctx)?;
                let target = Expr::parse(target_init, &ctx)?;
                Ok(ReductionRule {
                    params,
                    body: ReductionBody { source, target },
                })
            })
            .collect();

        let lambda_handler = create_lambda_handler(&root_ctx);

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

    pub fn get_expr_type(&self, expr: &Expr, ctx: &Context<Param>) -> Result<Expr, String> {
        match expr {
            Expr::Var(Var(idx)) => Ok(ctx.shifted_to_context(&ctx.get_var(*idx).type_expr, *idx)),
            Expr::App(app) => {
                let fun = &app.param;
                let arg = &app.body;
                let fun_type = self.get_expr_type(fun, ctx)?;
                let arg_type = self.get_expr_type(arg, ctx)?;
                let prop_param = Param {
                    name: None,
                    type_expr: self.lambda_handler.get_prop_type(arg_type.clone(), ctx),
                };
                let prop_var_ctx = ctx.with_local(&prop_param);
                let prop_var = Expr::var(-1);
                let arg_type_in_prop_var_ctx =
                    arg_type.with_shifted_vars(ctx.locals_start(), 0, -1);
                let cmp_fun_type = self.lambda_handler.get_pi_type(
                    arg_type_in_prop_var_ctx,
                    prop_var,
                    &prop_var_ctx,
                );
                if let Some(mut prop_vec) = fun_type.match_expr(
                    &Some(self),
                    &[prop_param],
                    &cmp_fun_type,
                    ctx.locals_start(),
                ) {
                    let prop = prop_vec.pop().unwrap();
                    Ok(Expr::apply(prop, arg.clone(), ctx))
                } else {
                    let fun_str = fun.print(ctx);
                    let fun_type_str = fun_type.print(ctx);
                    let arg_str = arg.print(ctx);
                    let arg_type_str = arg_type.print(ctx);
                    Err(format!("application type mismatch: {fun_str} : {fun_type_str} cannot be applied to {arg_str} : {arg_type_str}"))
                }
            }
            Expr::Lambda(lambda) => {
                let body_ctx = ctx.with_local(&lambda.param);
                let body_type = self.get_expr_type(&lambda.body, &body_ctx)?;
                let body_type_lambda = Expr::lambda(lambda.param.clone(), body_type);
                Ok(self.lambda_handler.get_pi_type(
                    lambda.param.type_expr.clone(),
                    body_type_lambda,
                    ctx,
                ))
            }
        }
    }

    pub fn check_reduction_rule_types(&self) -> Result<(), String> {
        let root_ctx = self.get_root_context();

        for rule in &self.reduction_rules {
            let ctx = root_ctx.with_locals(&rule.params);
            let source_type = self.get_expr_type(&rule.body.source, &ctx)?;
            let target_type = self.get_expr_type(&rule.body.target, &ctx)?;
            if !source_type.compare(ctx.locals_start(), &target_type, &Some(self)) {
                let source_str = rule.body.source.print(&ctx);
                let source_type_str = source_type.print(&ctx);
                let target_str = rule.body.target.print(&ctx);
                let target_type_str = target_type.print(&ctx);
                return Err(format!("type conflict in reduction rule between {source_str} : {source_type_str} and {target_str} : {target_type_str}"));
            }
        }

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

    pub fn apply(fun: Expr, arg: Expr, ctx: &Context<Param>) -> Self {
        if let Expr::Lambda(lambda) = fun {
            let mut expr = lambda.body;
            let locals_start = ctx.locals_start();
            expr.substitute(locals_start - 1, -1, &mut [arg], true);
            expr
        } else {
            Self::app(fun, arg)
        }
    }

    pub fn multi_apply(
        mut fun: Expr,
        args: SmallVec<[Expr; INLINE_PARAMS]>,
        ctx: &Context<Param>,
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
        for param in params {
            body = Self::lambda(param, body);
        }
        body
    }

    pub fn const_lambda(domain: Expr, mut body: Expr, ctx: &Context<Param>) -> Self {
        let param = Param {
            name: None,
            type_expr: domain,
        };
        body.shift_vars(ctx.locals_start(), 0, -1);
        Self::lambda(param, body)
    }

    pub fn parse(s: &str, ctx: &Context<Param>) -> Result<Self, String> {
        let mut parser_input = ParserInput(s);
        let mut parsing_context = ParsingContext {
            input: &mut parser_input,
            context: ctx,
        };
        parsing_context.parse()
    }

    pub fn print(&self, ctx: &Context<Param>) -> String {
        let mut result = String::new();
        let mut printing_context = PrintingContext {
            output: &mut result,
            context: ctx,
        };
        printing_context.print_expr(&self, false, false).unwrap();
        result
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

pub trait LambdaHandler {
    fn get_type_type(&self) -> Expr;

    fn get_pi_type(&self, domain: Expr, prop: Expr, ctx: &Context<Param>) -> Expr;

    fn get_fun_type(&self, domain: Expr, codomain: Expr, ctx: &Context<Param>) -> Expr {
        let prop = Expr::const_lambda(domain.clone(), codomain, ctx);
        self.get_pi_type(domain, prop, ctx)
    }

    fn get_prop_type(&self, domain: Expr, ctx: &Context<Param>) -> Expr {
        self.get_fun_type(domain, self.get_type_type(), ctx)
    }
}

struct ParsingContext<'a, 'b, 'c, 'd: 'c> {
    input: &'a mut ParserInput<'b>,
    context: &'a Context<'c, 'd, 'a, Param>,
}

impl<'a, 'b, 'c, 'd> ParsingContext<'a, 'b, 'c, 'd> {
    fn parse(&mut self) -> Result<Expr, String> {
        if let Some(mut expr) = self.try_parse_one()? {
            while let Some(arg) = self.try_parse_one()? {
                expr = Expr::app(expr, arg);
            }
            Ok(expr)
        } else {
            self.input.expected("expression")
        }
    }

    fn try_parse_one(&mut self) -> Result<Option<Expr>, String> {
        self.input.skip_whitespace();
        if self.input.try_read_char('(') {
            let expr = self.parse()?;
            self.input.read_char(')')?;
            Ok(Some(expr))
        } else if self.input.try_read_char('λ') {
            self.input.skip_whitespace();
            if let Some(param_name_str) = self.input.try_read_name() {
                let param_name = String::from(param_name_str);
                self.input.read_char(':')?;
                let param_type = self.parse()?;
                self.input.read_char('.')?;
                let param = Param {
                    name: Some(Rc::new(param_name)),
                    type_expr: param_type,
                };
                let mut body_ctx = ParsingContext {
                    input: self.input,
                    context: &self.context.with_local(&param),
                };
                let body = body_ctx.parse()?;
                Ok(Some(Expr::lambda(param, body)))
            } else {
                self.input.expected("identifier")
            }
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
}

struct PrintingContext<'a, 'b, 'c: 'b, W: fmt::Write> {
    output: &'a mut W,
    context: &'a Context<'b, 'c, 'a, Param>,
}

impl<'a, 'b, 'c, W: fmt::Write> PrintingContext<'a, 'b, 'c, W> {
    fn print_expr(
        &mut self,
        expr: &Expr,
        parens_for_app: bool,
        parens_for_lambda: bool,
    ) -> fmt::Result {
        match expr {
            Expr::Var(Var(idx)) => self.context.get_var(*idx).print_name(self.output)?,
            Expr::App(app) => {
                if parens_for_app {
                    self.output.write_char('(')?;
                }
                self.print_expr(&app.param, false, true)?;
                self.output.write_char(' ')?;
                self.print_expr(&app.body, true, true)?;
                if parens_for_app {
                    self.output.write_char(')')?;
                }
            }
            Expr::Lambda(lambda) => {
                if parens_for_lambda {
                    self.output.write_char('(')?;
                }
                self.output.write_str("λ ")?;
                self.print_param(&lambda.param)?;
                self.output.write_str(". ")?;
                let mut body_ctx = PrintingContext {
                    output: self.output,
                    context: &self.context.with_local(&lambda.param),
                };
                body_ctx.print_expr(&lambda.body, false, false)?;
                if parens_for_lambda {
                    self.output.write_char(')')?;
                }
            }
        }
        Ok(())
    }

    fn print_param(&mut self, param: &Param) -> fmt::Result {
        param.print_name(self.output)?;
        self.output.write_str(" : ")?;
        self.print_expr(&param.type_expr, false, false)?;
        Ok(())
    }
}

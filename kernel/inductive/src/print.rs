use std::fmt;

use symbol_table::Symbol;

use slate_kernel_generic::{context::*, context_object::*, expr_parts::*};
use slate_kernel_util::printer::*;

use crate::{context::*, expr::*, theory::*};

pub struct PrintingContext<'a, 'b, W: fmt::Write> {
    output: &'a mut W,
    context: &'a InductiveContext<'b>,
}

impl<W: fmt::Write> PrintingContext<'_, '_, W> {
    pub fn print(
        result: &mut W,
        ctx: &InductiveContext,
        f: impl FnOnce(&mut PrintingContext<W>) -> fmt::Result,
    ) -> fmt::Result {
        let mut printing_context = PrintingContext {
            output: result,
            context: ctx,
        };
        f(&mut printing_context)
    }

    pub fn print_term(&mut self, tm: &Term, outer_precedence: isize) -> fmt::Result {
        match tm {
            Term::Placeholder => self.print_placeholder(),
            Term::Var(var) => self.print_var(var, outer_precedence),
            Term::Ctor(ctor_ref) => self.print_ctor_ref(ctor_ref),
            Term::Match(match_tm) => self.print_match_term(match_tm),
        }
    }

    pub fn print_type(&mut self, ty: &Type, outer_precedence: isize) -> fmt::Result {
        match ty {
            Type::Placeholder => self.print_placeholder(),
            Type::Var(var) => self.print_var(var, outer_precedence),
            Type::Data(data_type) => self.print_data_type(data_type),
        }
    }

    fn with_param_decls(
        &mut self,
        params: &[Param],
        f: impl FnOnce(&mut PrintingContext<W>) -> fmt::Result,
    ) -> fmt::Result {
        self.print_param_decls(params)?;

        self.context.with_locals(params, |context| {
            let mut printing_context = PrintingContext {
                output: self.output,
                context,
            };
            f(&mut printing_context)
        })
    }

    fn print_param_decls(&mut self, params: &[Param]) -> fmt::Result {
        let mut iter = params.iter();
        if let Some(param) = iter.next() {
            self.output.write_char('[')?;
            self.print_param_decl(param)?;
            while let Some(param) = iter.next() {
                self.output.write_str(", ")?;
                self.print_param_decl(param)?;
            }
            self.output.write_char(']')?;
        }

        Ok(())
    }

    fn print_param_decl(&mut self, param: &Param) -> fmt::Result {
        self.print_parameterized_object(param, |params_ctx, kind| params_ctx.print_param_kind(kind))
    }

    fn print_parameterized_object<Data: ContextObject>(
        &mut self,
        obj: &Parameterized<Data>,
        print_data: impl FnOnce(&mut PrintingContext<W>, &Data) -> fmt::Result,
    ) -> fmt::Result {
        let param_params = &obj.data.params;
        self.with_param_decls(param_params, |params_ctx| {
            let param_args = get_param_args(params_ctx.context, param_params.len());
            params_ctx.print_application(&obj.notation, &param_args, 0)?;
            print_data(params_ctx, &obj.data.body)
        })
    }

    fn print_param_kind(&mut self, kind: &ParamKind) -> fmt::Result {
        match kind {
            ParamKind::TypeParam => self.output.write_str(" type"),
            ParamKind::TermParam(ty) => {
                self.output.write_str(": ")?;
                self.print_type(ty, 0)
            }
            ParamKind::DefParam(def) => {
                self.output.write_str(": ")?;
                self.print_param_kind(&def.kind)?;
                self.output.write_str(" := ")?;
                self.print_arg_value(&def.value, 0)
            }
        }
    }

    fn print_placeholder(&mut self) -> fmt::Result {
        self.output.write_char('_')
    }

    fn print_var(&mut self, var: &VarRef, outer_precedence: isize) -> fmt::Result {
        let param = self.context.get_var(var.body.0);
        self.print_application(&param.notation, &var.params, outer_precedence)
    }

    fn print_application(
        &mut self,
        notation: &Notation,
        args: &[Arg],
        outer_precedence: isize,
    ) -> fmt::Result {
        if notation.precedence <= outer_precedence {
            self.output.write_char('(')?;
        }

        if let Some(left_arg_idx) = notation.left_arg {
            self.print_arg(&args[left_arg_idx.get()], notation.precedence)?;
        }

        self.print_fun(&notation.sym, args)?;
        self.print_args(&notation.fun_args, args)?;

        if let Some(right_arg_idx) = notation.right_arg {
            self.print_arg(&args[right_arg_idx.get()], notation.precedence)?;
        }

        if notation.precedence <= outer_precedence {
            self.output.write_char(')')?;
        }

        Ok(())
    }

    fn print_fun(&mut self, fun_sym: &FunctionSymbol, args: &[Arg]) -> fmt::Result {
        match fun_sym {
            FunctionSymbol::Name(sym) => self.print_symbol(*sym),
            FunctionSymbol::Arg(arg_idx) => self.print_arg(&args[*arg_idx], isize::MAX),
        }
    }

    fn print_symbol(&mut self, sym: Symbol) -> fmt::Result {
        let name = self.context.resolve_name(sym);
        print_identifier(name, self.output)
    }

    fn print_arg(&mut self, arg: &Arg, outer_precedence: isize) -> fmt::Result {
        if arg.params.is_empty() {
            self.print_arg_value(&arg.body, outer_precedence)
        } else {
            if outer_precedence > 0 {
                self.output.write_char('(')?;
            }

            self.with_param_decls(&arg.params, |arg_value_ctx| {
                arg_value_ctx.print_arg_value(&arg.body, 0)
            })?;

            if outer_precedence > 0 {
                self.output.write_char(')')?;
            }

            Ok(())
        }
    }

    fn print_arg_value(&mut self, arg_value: &ArgValue, outer_precedence: isize) -> fmt::Result {
        match arg_value {
            ArgValue::TypeArg(ty) => self.print_type(ty, outer_precedence),
            ArgValue::TermArg(tm) => self.print_term(tm, outer_precedence),
            ArgValue::DefArg => self.print_placeholder(),
        }
    }

    fn print_args(&mut self, fun_args: &[usize], args: &[Arg]) -> fmt::Result {
        let mut iter = fun_args.iter();
        if let Some(arg_idx) = iter.next() {
            self.output.write_char('(')?;
            self.print_arg(&args[*arg_idx], 0)?;
            while let Some(arg_idx) = iter.next() {
                self.output.write_str(", ")?;
                self.print_arg(&args[*arg_idx], 0)?;
            }
            self.output.write_char(')')?;
        }

        Ok(())
    }

    fn print_data_type(&mut self, data_type: &DataType) -> fmt::Result {
        self.output.write_char('{')?;

        let mut print_separator = false;
        for ctor in &data_type.ctors {
            if print_separator {
                self.output.write_str(" | ")?;
            }
            self.print_ctor(ctor)?;
            print_separator = true;
        }

        self.output.write_char('}')?;

        Ok(())
    }

    fn print_ctor(&mut self, ctor: &Ctor) -> fmt::Result {
        self.print_parameterized_object(ctor, |_, _| Ok(()))
    }

    fn print_ctor_ref(&mut self, ctor_ref: &CtorRef) -> fmt::Result {
        self.print_type(&ctor_ref.type_ref, isize::MAX)?;
        todo!()
    }

    fn print_match_term(&mut self, match_tm: &MatchTerm) -> fmt::Result {
        todo!()
    }
}

fn get_param_args(ctx: &InductiveContext, len: usize) -> InlineVec<Arg> {
    (-(len as VarIndex)..0)
        .map(|idx| get_param_arg(ctx, idx))
        .collect()
}

fn get_param_arg(ctx: &InductiveContext, idx: VarIndex) -> Arg {
    let param = ctx.get_var(idx);
    let mut var = Var(idx);
    let arg_params = param.data.params.clone();
    let arg_value =
        ctx.with_locals(&arg_params, |arg_params_ctx| {
            var.shift_to_subcontext(ctx, arg_params_ctx);
            match param.data.body {
                ParamKind::TypeParam => ArgValue::TypeArg(Type::Var(Box::new(
                    make_param_arg_var_ref(var, &arg_params, arg_params_ctx),
                ))),
                ParamKind::TermParam(_) => ArgValue::TermArg(Term::Var(Box::new(
                    make_param_arg_var_ref(var, &arg_params, arg_params_ctx),
                ))),
                ParamKind::DefParam(_) => ArgValue::DefArg,
            }
        });
    Box::new(MultiLambda {
        params: arg_params,
        body: arg_value,
    })
}

fn make_param_arg_var_ref(
    var: Var,
    arg_params: &[Param],
    arg_params_ctx: &InductiveContext,
) -> VarRef {
    let param_args = get_param_args(arg_params_ctx, arg_params.len());
    MultiApp {
        params: param_args,
        body: var,
    }
}

use nonminmax::NonMaxUsize;
use symbol_table::Symbol;

use slate_kernel_generic::{
    context::*, context_object::*, expr_parts::*, primitive_context_object,
};
use slate_kernel_generic_derive::*;

#[derive(Clone, PartialEq, ContextObject)]
pub enum Type {
    Placeholder,
    Var(Box<VarRef>),
    Data(Box<DataType>),
}

impl Default for Type {
    fn default() -> Self {
        Type::Placeholder
    }
}

#[derive(Clone, PartialEq, ContextObject)]
pub enum Term {
    Placeholder,
    Var(Box<VarRef>),
    Ctor(Box<CtorRef>),
    Match(Box<MatchTerm>),
}

impl Default for Term {
    fn default() -> Self {
        Term::Placeholder
    }
}

#[derive(Clone)]
pub struct Notation {
    pub sym: FunctionSymbol,
    pub precedence: isize,
    pub left_arg: Option<NonMaxUsize>,
    pub right_arg: Option<NonMaxUsize>,
    pub fun_args: InlineVec<usize>,
}

impl NamedObject<SymbolDesc> for Notation {
    fn get_name(&self) -> SymbolDesc {
        SymbolDesc {
            name_or_arg: match self.sym {
                FunctionSymbol::Name(sym) => Some(sym),
                FunctionSymbol::Arg(_) => None,
            },
            has_left_arg: self.left_arg.is_some(),
            has_right_arg: self.right_arg.is_some(),
        }
    }
}

impl PartialEq for Notation {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

primitive_context_object!(Notation);

#[derive(Clone, Copy)]
pub enum FunctionSymbol {
    Name(Symbol),
    Arg(usize),
}

#[derive(Clone, Copy, PartialEq)]
pub struct SymbolDesc {
    pub name_or_arg: Option<Symbol>,
    pub has_left_arg: bool,
    pub has_right_arg: bool,
}

#[derive(Clone, PartialEq, ContextObject)]
pub struct Parameterized<Data: ContextObject> {
    pub data: WithParams<Data>,
    pub notation: Notation,
}

pub type Param = Box<Parameterized<ParamKind>>;

impl NamedObject<SymbolDesc> for Param {
    fn get_name(&self) -> SymbolDesc {
        self.notation.get_name()
    }
}

#[derive(Clone, PartialEq, ContextObject)]
pub enum ParamKind {
    TypeParam,
    TermParam(Type),
    DefParam(Box<DefinitionContents>),
}

pub type Arg = Box<WithParams<ArgValue>>;

#[derive(Clone, PartialEq, ContextObject)]
pub enum ArgValue {
    TypeArg(Type),
    TermArg(Term),
    DefArg,
}

pub type WithParams<T> = MultiLambda<Param, T>;
pub type WithArgs<T> = MultiApp<T, Arg>;

pub type VarRef = WithArgs<Var>;

#[derive(Clone, PartialEq, ContextObject)]
pub struct DataType {
    pub ctors: InlineVec<Ctor>,
}

pub type Ctor = Parameterized<()>;

#[derive(Clone, PartialEq, ContextObject)]
pub struct CtorRef {
    pub type_ref: Type,
    pub ctor_ref: WithArgs<usize>,
}

#[derive(Clone, PartialEq, ContextObject)]
pub struct MatchTerm {
    pub match_type: Type,
    pub match_term: Term,
    pub result_type: Type,
    pub arms: InlineVec<WithParams<Term>>,
}

#[derive(Clone, PartialEq, ContextObject)]
pub struct DefinitionContents {
    pub kind: ParamKind,
    pub value: ArgValue,
}

#[derive(Clone, PartialEq)]
pub struct Definition {
    pub param: Param,
    pub value: ArgValue,
}

impl Definition {
    pub fn contents(self) -> WithParams<DefinitionContents> {
        WithParams {
            params: self.param.data.params,
            body: DefinitionContents {
                kind: self.param.data.body,
                value: self.value,
            },
        }
    }
}

impl NamedObject<SymbolDesc> for Definition {
    fn get_name(&self) -> SymbolDesc {
        self.param.get_name()
    }
}

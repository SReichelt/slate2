use slate_kernel_generic::context::*;

use crate::{expr::*, theory::*};

#[derive(Clone, Copy)]
pub struct InductiveContextOptions {
    pub reduce_with_reduction_rules: bool,
    pub reduce_with_combinators: bool,
    pub print_all_implicit_args: bool,
}

#[derive(Clone, Copy)]
pub struct InductiveContextData<'a> {
    pub theory: &'a InductiveTheory,
    pub options: InductiveContextOptions,
}

impl VarAccessor<Param> for InductiveContextData<'_> {
    fn get_var(&self, idx: VarIndex) -> &Param {
        self.theory.get_var(idx)
    }

    fn for_each_var<R>(&self, f: impl FnMut(VarIndex, &Param) -> Option<R>) -> Option<R> {
        self.theory.for_each_var(f)
    }
}

pub type InductiveContext<'a> = ParamContextImpl<Param, InductiveContextData<'a>>;

impl InductiveTheoryRef for InductiveContext<'_> {
    fn theory(&self) -> &InductiveTheory {
        self.extra_data().theory
    }
}

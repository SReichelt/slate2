use slate_kernel_generic::context::*;

use crate::{expr::*, metalogic::*};

#[derive(Clone, Copy)]
pub struct MetaLogicContextOptions {
    pub reduce_with_reduction_rules: bool,
    pub reduce_with_combinators: bool,
    pub print_all_implicit_args: bool,
}

#[derive(Clone, Copy)]
pub struct MetaLogicContextData<'a> {
    pub metalogic: &'a MetaLogic,
    pub options: MetaLogicContextOptions,
}

impl VarAccessor<Param> for MetaLogicContextData<'_> {
    fn get_var(&self, idx: VarIndex) -> &Param {
        self.metalogic.get_var(idx)
    }

    fn for_each_var<R>(&self, f: impl FnMut(VarIndex, &Param) -> Option<R>) -> Option<R> {
        self.metalogic.for_each_var(f)
    }
}

pub type MetaLogicContext<'a> = ParamContextImpl<Param, MetaLogicContextData<'a>>;

impl MetaLogicRef for MetaLogicContext<'_> {
    fn metalogic(&self) -> &MetaLogic {
        self.extra_data().metalogic
    }
}

pub trait OptionContext<Options> {
    fn options(&self) -> &Options;

    fn with_new_options<R>(
        &self,
        options: MetaLogicContextOptions,
        f: impl FnOnce(&Self) -> R,
    ) -> R;
}

impl OptionContext<MetaLogicContextOptions> for MetaLogicContext<'_> {
    fn options(&self) -> &MetaLogicContextOptions {
        &self.extra_data().options
    }

    fn with_new_options<R>(
        &self,
        options: MetaLogicContextOptions,
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        let extra_data = MetaLogicContextData {
            options,
            ..*self.extra_data()
        };
        self.with_new_extra_data(extra_data, f)
    }
}

/// We distinguish between comparisons with or without reductions by passing either
/// `MetaLogicContext` or `MinimalContext`.
pub trait ComparisonContext: ParamContext<Param> {
    fn as_metalogic_context(&self) -> Option<&MetaLogicContext>;

    fn use_combinators(&self) -> bool;
}

// We need this so that with_reduction_options can take a single closure instead of two, which is
// necessary because we would need to mutate the same variable in both closures.
pub enum ReductionOptionParam<'a, 'b, Ctx: ComparisonContext> {
    NoRed(&'a Ctx),
    Red(&'a MetaLogicContext<'b>),
}

impl ComparisonContext for MinimalContext {
    fn as_metalogic_context(&self) -> Option<&MetaLogicContext> {
        None
    }

    fn use_combinators(&self) -> bool {
        false
    }
}

impl ComparisonContext for MetaLogicContext<'_> {
    fn as_metalogic_context(&self) -> Option<&MetaLogicContext> {
        Some(self)
    }

    fn use_combinators(&self) -> bool {
        self.extra_data().options.reduce_with_combinators
    }
}

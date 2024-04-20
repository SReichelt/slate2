use anyhow::{anyhow, Error, Result};
use log::{trace, warn};
use symbol_table::{Symbol, SymbolTable};

use slate_kernel_generic::{context::*, context_object::*, expr_parts::*};
use slate_kernel_util::{anyhow::*, parser::*};

use crate::{context::*, expr::*};

pub struct InductiveTheory {
    symbol_table: SymbolTable,
    definitions: Vec<Definition>,
    config: InductiveConfig,
    pub root_ctx_options: InductiveContextOptions,
}

impl InductiveTheory {
    pub fn get_root_context(&self) -> InductiveContext {
        self.get_root_context_with_options(self.root_ctx_options)
    }

    pub fn get_root_context_with_options(
        &self,
        options: InductiveContextOptions,
    ) -> InductiveContext {
        InductiveContext::new(InductiveContextData {
            theory: self,
            options,
        })
    }
}

impl VarAccessor<Param> for InductiveTheory {
    fn get_var(&self, idx: VarIndex) -> &Param {
        &self.definitions.get_var(idx).param
    }

    fn for_each_var<R>(&self, mut f: impl FnMut(VarIndex, &Param) -> Option<R>) -> Option<R> {
        self.definitions
            .for_each_var(|var_idx, constant| f(var_idx, &constant.param))
    }
}

pub trait InductiveTheoryRef {
    fn theory(&self) -> &InductiveTheory;

    fn definitions(&self) -> &[Definition] {
        &self.theory().definitions
    }

    fn config(&self) -> &InductiveConfig {
        &self.theory().config
    }

    fn intern_name(&self, name: &str) -> Symbol {
        self.theory().symbol_table.intern(name)
    }

    fn resolve_name(&self, sym: Symbol) -> &str {
        self.theory().symbol_table.resolve(sym)
    }
}

impl InductiveTheoryRef for InductiveTheory {
    fn theory(&self) -> &InductiveTheory {
        self
    }
}

pub struct InductiveConfig;

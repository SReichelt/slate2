use std::collections::HashMap;

use anyhow::Result;

use slate_kernel_generic::context::*;

use crate::metalogic::*;

pub enum ModuleInit<'a> {
    Const(ConstInit<'a>),
    Type {
        ctor: ConstInit<'a>,
        defs: &'a [ModuleInit<'a>],
    },
}

impl MetaLogic {
    pub fn construct_semantically<F>(modules_init: &[ModuleInit], get_config: F) -> Result<Self>
    where
        F: FnOnce(&HashMap<String, VarIndex>) -> MetaLogicConfig,
    {
        let mut constants_init: Vec<&ConstInit> = Vec::new();
        Self::add_modules(modules_init, &mut constants_init);
        Self::construct(&constants_init, get_config)
    }

    fn add_modules<'a>(
        modules_init: &'a [ModuleInit<'a>],
        constants_init: &mut Vec<&'a ConstInit<'a>>,
    ) {
        for module_init in modules_init {
            match module_init {
                ModuleInit::Const(constant_init) => {
                    Self::add_constant(constant_init, constants_init);
                }
                ModuleInit::Type { ctor, defs } => {
                    Self::add_constant(ctor, constants_init);
                    Self::add_modules(defs, constants_init);
                }
            }
        }
    }

    fn add_constant<'a>(
        constant_init: &'a ConstInit<'a>,
        constants_init: &mut Vec<&'a ConstInit<'a>>,
    ) {
        constants_init.push(constant_init);
    }
}

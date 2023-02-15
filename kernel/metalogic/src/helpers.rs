use std::{borrow::Cow, collections::HashMap};

use anyhow::Result;

use slate_kernel_generic::context::*;

use crate::metalogic::*;

pub enum ModuleInit<'a> {
    Def(DefInit<'a>),
    Type {
        ctor: DefInit<'a>,
        defs: &'a [ModuleInit<'a>],
    },
}

impl MetaLogic {
    pub fn construct_semantically<F>(
        modules_init: &[ModuleInit],
        create_lambda_handler: F,
    ) -> Result<Self>
    where
        F: FnOnce(&HashMap<&str, VarIndex>) -> Box<dyn LambdaHandler>,
    {
        let mut constants_init: Vec<Cow<DefInit>> = Vec::new();
        Self::add_modules(modules_init, &mut constants_init);
        Self::construct(&constants_init, create_lambda_handler)
    }

    fn add_modules<'a>(
        modules_init: &'a [ModuleInit<'a>],
        constants_init: &mut Vec<Cow<'a, DefInit<'a>>>,
    ) {
        for module_init in modules_init {
            match module_init {
                ModuleInit::Def(def_init) => Self::add_def(def_init, constants_init),
                ModuleInit::Type { ctor, defs } => {
                    Self::add_def(ctor, constants_init);
                    Self::add_modules(defs, constants_init);
                }
            }
        }
    }

    fn add_def<'a>(def_init: &'a DefInit<'a>, constants_init: &mut Vec<Cow<'a, DefInit<'a>>>) {
        constants_init.push(Cow::Borrowed(def_init));
    }
}

use anyhow::Result;

use super::{expr::*, metalogic::*};

pub struct TypeInit<'a> {
    pub ctor: DefInit<'a>,
    pub defs: &'a [DefInit<'a>],
}

pub struct DefInit<'a> {
    pub sym: &'a str,
    pub red: &'a [&'a str],
}

impl MetaLogic {
    pub fn construct_semantically<F>(
        types_init: &[TypeInit],
        defs_init: &[DefInit],
        create_lambda_handler: F,
    ) -> Result<Self>
    where
        F: FnOnce(&[Param]) -> Box<dyn LambdaHandler>,
    {
        let mut constants_init: Vec<&str> = Vec::new();
        let mut reduction_rules_init: Vec<&str> = Vec::new();

        Self::add_types(types_init, &mut constants_init, &mut reduction_rules_init);
        Self::add_defs(defs_init, &mut constants_init, &mut reduction_rules_init);

        Self::construct(
            &constants_init,
            &reduction_rules_init,
            create_lambda_handler,
        )
    }

    fn add_types<'a>(
        types_init: &[TypeInit<'a>],
        constants_init: &mut Vec<&'a str>,
        reduction_rules_init: &mut Vec<&'a str>,
    ) {
        for type_init in types_init {
            Self::add_type(type_init, constants_init, reduction_rules_init);
        }
    }

    fn add_type<'a>(
        type_init: &TypeInit<'a>,
        constants_init: &mut Vec<&'a str>,
        reduction_rules_init: &mut Vec<&'a str>,
    ) {
        Self::add_def(&type_init.ctor, constants_init, reduction_rules_init);
        Self::add_defs(type_init.defs, constants_init, reduction_rules_init);
    }

    fn add_defs<'a>(
        defs_init: &[DefInit<'a>],
        constants_init: &mut Vec<&'a str>,
        reduction_rules_init: &mut Vec<&'a str>,
    ) {
        for def_init in defs_init {
            Self::add_def(def_init, constants_init, reduction_rules_init);
        }
    }

    fn add_def<'a>(
        def_init: &DefInit<'a>,
        constants_init: &mut Vec<&'a str>,
        reduction_rules_init: &mut Vec<&'a str>,
    ) {
        constants_init.push(def_init.sym);
        Self::add_reduction_rules(def_init.red, reduction_rules_init);
    }

    fn add_reduction_rules<'a>(rules_init: &[&'a str], reduction_rules_init: &mut Vec<&'a str>) {
        for rule_init in rules_init {
            reduction_rules_init.push(*rule_init);
        }
    }
}

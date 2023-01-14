use super::{expr::*, metalogic::*};

use crate::generic::context::*;

pub struct TypeInit<'a> {
    pub ctor: ParamInit<'a>,
    pub intro: &'a [ParamInit<'a>],
    pub elim: &'a [ParamInit<'a>],
    pub red: &'a [ReductionRuleInit<'a>],
}

pub struct DefInit<'a> {
    pub sym: ParamInit<'a>,
    pub red: &'a [ReductionRuleInit<'a>],
}

impl MetaLogic {
    pub fn construct_semantically<F>(
        types_init: &[TypeInit],
        defs_init: &[DefInit],
        create_lambda_handler: F,
    ) -> Result<Self, String>
    where
        F: FnOnce(&Context<Param>) -> Box<dyn LambdaHandler>,
    {
        let mut constants_init: Vec<ParamInit> = Vec::new();
        let mut reduction_rules_init: Vec<ReductionRuleInit> = Vec::new();

        for type_init in types_init {
            constants_init.push(type_init.ctor);
            for intro_init in type_init.intro {
                constants_init.push(*intro_init);
            }
            for elim_init in type_init.elim {
                constants_init.push(*elim_init);
            }
            for red_init in type_init.red {
                reduction_rules_init.push(*red_init);
            }
        }

        for def_init in defs_init {
            constants_init.push(def_init.sym);
            for red_init in def_init.red {
                reduction_rules_init.push(*red_init);
            }
        }

        Self::construct(
            &constants_init,
            &reduction_rules_init,
            create_lambda_handler,
        )
    }
}

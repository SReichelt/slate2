use std::{fmt::Debug, rc::Rc};

use anyhow::Result;

pub trait MetaModelGetter {
    fn metamodel(&self, name: &str) -> Result<MetaModelRef>;
}

pub trait MetaModel {
    fn name(&self) -> &str;

    fn is_definition_symbol(&self, s: &str) -> bool;

    fn parameterization(&self, start_paren: char) -> Option<&dyn Parameterization>;
    fn object(&self, start_paren: char) -> Option<&dyn Object>;
}

#[derive(Clone)]
pub struct MetaModelRef(pub Rc<dyn MetaModel>);

impl MetaModelRef {
    pub fn new(metamodel: impl MetaModel + 'static) -> Self {
        MetaModelRef(Rc::new(metamodel))
    }
}

impl PartialEq for MetaModelRef {
    fn eq(&self, other: &Self) -> bool {
        self.0.name() == other.0.name()
    }
}

impl Debug for MetaModelRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = self.0.name();
        f.write_fmt(format_args!("MetaModel({name})"))
    }
}

pub trait Parameterization {}

pub trait Object {
    fn param_delimiter(&self) -> Option<char>;
}

#[cfg(test)]
pub mod test_helpers {
    use anyhow::anyhow;

    use super::*;

    pub struct TestMetaModelGetter;

    impl MetaModelGetter for TestMetaModelGetter {
        fn metamodel(&self, name: &str) -> Result<MetaModelRef> {
            match name {
                "test" => Ok(TestMetaModel::new_ref()),
                name => Err(anyhow!("unknown metamodel '{name}'")),
            }
        }
    }

    pub struct TestMetaModel {
        bracket_parameterization: TestParameterization,
        brace_object: TestObject,
    }

    impl TestMetaModel {
        pub fn new_ref() -> MetaModelRef {
            MetaModelRef::new(TestMetaModel {
                bracket_parameterization: TestParameterization,
                brace_object: TestObject,
            })
        }
    }

    impl MetaModel for TestMetaModel {
        fn name(&self) -> &str {
            "test"
        }

        fn is_definition_symbol(&self, s: &str) -> bool {
            s.starts_with(':')
        }

        fn parameterization(&self, start_paren: char) -> Option<&dyn Parameterization> {
            match start_paren {
                '[' | '⟦' => Some(&self.bracket_parameterization),
                _ => None,
            }
        }

        fn object(&self, start_paren: char) -> Option<&dyn Object> {
            match start_paren {
                '{' => Some(&self.brace_object),
                _ => None,
            }
        }
    }

    struct TestParameterization;

    impl Parameterization for TestParameterization {}

    struct TestObject;

    impl Object for TestObject {
        fn param_delimiter(&self) -> Option<char> {
            Some('|')
        }
    }
}

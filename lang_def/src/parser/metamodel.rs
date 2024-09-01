use std::fmt::Debug;

use lang_def::impl_mem_serializable_self;

pub trait MetaModelGetter {
    fn metamodel(&self, name: &str) -> Option<&dyn MetaModel>;
}

pub trait MetaModelPart: Debug {
    /// Used to implement [`Eq`] on trait object references.
    fn id(&self) -> usize;
}

macro_rules! meta_model_part {
    ($($trait:tt)+) => {
        impl PartialEq for &dyn $($trait)+ {
            fn eq(&self, other: &Self) -> bool {
                MetaModelPart::id(*self) == MetaModelPart::id(*other)
            }
        }

        impl Eq for &dyn $($trait)+ {}

        impl_mem_serializable_self!(&'static dyn $($trait)+);
    };
}

pub trait MetaModel: MetaModelPart {
    fn name(&self) -> &str;

    // The section which implicitly surrounds the entire document.
    fn top_level_section_kind(&self) -> &dyn SectionKind;
}

meta_model_part!(MetaModel);

pub trait SectionKind: MetaModelPart {
    fn parameterization(&self, paren: char) -> Option<&dyn SectionKind>;
    fn data_kind(&self) -> &dyn DataKind;
    fn param_kind(&self) -> &dyn ParamKind;
    fn subsection(&self, paren: char) -> Option<&dyn SectionKind>;
    fn notation_prefixes(&self) -> Option<NotationPrefixOptions>;
}

meta_model_part!(SectionKind);

pub struct NotationPrefixOptions {
    pub paren: char,
}

pub trait ParamKind: MetaModelPart {
    fn keyword_is_notation_delimiter(&self, keyword: &str) -> bool;
    fn identifier_is_notation_delimiter(&self, identifier: &str) -> bool;
    fn paren_is_notation_delimiter(&self, paren: char) -> bool;
}

meta_model_part!(ParamKind);

pub trait MappingKind: MetaModelPart {
    fn param_kind(&self) -> &dyn ParamKind;
}

meta_model_part!(MappingKind);

pub trait InfixMappingKind: MappingKind {
    fn binder_paren(&self) -> char;

    fn as_mapping_kind(&self) -> &dyn MappingKind;
}

meta_model_part!(InfixMappingKind);

pub trait DataKind: MetaModelPart {
    fn parameterization(&self, paren: char) -> Option<&dyn SectionKind>;
    fn special_data_kind(&self, paren: char) -> Option<&dyn DataKind>;
    fn prefix_mapping_kind(&self, identifier: &str) -> Option<&dyn MappingKind>;
    fn infix_mapping_kind(&self, identifier: &str) -> Option<&dyn InfixMappingKind>;
    fn object_kind(&self, paren: char) -> Option<&dyn ObjectKind>;
}

meta_model_part!(DataKind);

pub trait ObjectKind: MetaModelPart {
    fn separator(&self) -> char;

    fn parameterization(&self) -> &dyn SectionKind;
    fn param_data_kind(&self) -> &dyn DataKind;
    fn param_kind(&self) -> &dyn ParamKind;
    fn extra_part_kind(&self, extra_part_idx: usize) -> Option<&dyn SectionKind>;
}

meta_model_part!(ObjectKind);

#[cfg(test)]
pub mod testing {
    use super::*;

    #[derive(Debug)]
    pub struct TestMetaModel;

    impl MetaModelPart for TestMetaModel {
        fn id(&self) -> usize {
            0
        }
    }

    impl MetaModelGetter for TestMetaModel {
        fn metamodel(&self, name: &str) -> Option<&dyn MetaModel> {
            match name {
                "test" => Some(self),
                _ => None,
            }
        }
    }

    impl MetaModel for TestMetaModel {
        fn name(&self) -> &str {
            "test"
        }

        fn top_level_section_kind(&self) -> &dyn SectionKind {
            self
        }
    }

    impl SectionKind for TestMetaModel {
        fn parameterization(&self, paren: char) -> Option<&dyn SectionKind> {
            match paren {
                '[' => Some(self),
                _ => None,
            }
        }

        fn data_kind(&self) -> &dyn DataKind {
            self
        }

        fn param_kind(&self) -> &dyn ParamKind {
            self
        }

        fn subsection(&self, paren: char) -> Option<&dyn SectionKind> {
            match paren {
                '{' => Some(self),
                _ => None,
            }
        }

        fn notation_prefixes(&self) -> Option<NotationPrefixOptions> {
            Some(NotationPrefixOptions { paren: '(' })
        }
    }

    impl ParamKind for TestMetaModel {
        fn keyword_is_notation_delimiter(&self, keyword: &str) -> bool {
            keyword == "%Type"
        }

        fn identifier_is_notation_delimiter(&self, identifier: &str) -> bool {
            identifier.starts_with(':') || identifier == "↦"
        }

        fn paren_is_notation_delimiter(&self, paren: char) -> bool {
            paren == '⎿'
        }
    }

    #[derive(Debug)]
    pub struct TestPrefixMapping;

    impl MetaModelPart for TestPrefixMapping {
        fn id(&self) -> usize {
            0
        }
    }

    impl MappingKind for TestPrefixMapping {
        fn param_kind(&self) -> &dyn ParamKind {
            &TestMetaModel
        }
    }

    #[derive(Debug)]
    pub struct TestInfixMapping;

    impl MetaModelPart for TestInfixMapping {
        fn id(&self) -> usize {
            1
        }
    }

    impl MappingKind for TestInfixMapping {
        fn param_kind(&self) -> &dyn ParamKind {
            &TestMetaModel
        }
    }

    impl InfixMappingKind for TestInfixMapping {
        fn binder_paren(&self) -> char {
            '('
        }

        fn as_mapping_kind(&self) -> &dyn MappingKind {
            self
        }
    }

    impl DataKind for TestMetaModel {
        fn parameterization(&self, paren: char) -> Option<&dyn SectionKind> {
            match paren {
                '[' => Some(self),
                _ => None,
            }
        }

        fn special_data_kind(&self, _paren: char) -> Option<&dyn DataKind> {
            None
        }

        fn prefix_mapping_kind(&self, identifier: &str) -> Option<&dyn MappingKind> {
            match identifier {
                "λ" => Some(&TestPrefixMapping),
                _ => None,
            }
        }

        fn infix_mapping_kind(&self, identifier: &str) -> Option<&dyn InfixMappingKind> {
            match identifier {
                "↦" => Some(&TestInfixMapping),
                _ => None,
            }
        }

        fn object_kind(&self, paren: char) -> Option<&dyn ObjectKind> {
            match paren {
                '{' => Some(self),
                _ => None,
            }
        }
    }

    impl ObjectKind for TestMetaModel {
        fn separator(&self) -> char {
            '|'
        }

        fn parameterization(&self) -> &dyn SectionKind {
            self
        }

        fn param_data_kind(&self) -> &dyn DataKind {
            self
        }

        fn param_kind(&self) -> &dyn ParamKind {
            self
        }

        fn extra_part_kind(&self, extra_part_idx: usize) -> Option<&dyn SectionKind> {
            if extra_part_idx < 2 {
                Some(self)
            } else {
                None
            }
        }
    }
}

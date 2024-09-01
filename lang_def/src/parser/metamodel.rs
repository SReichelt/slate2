use std::fmt::Debug;

use lang_def::impl_mem_serializable_self;

pub trait MetaModelGetter {
    fn metamodel(&self, name: &str) -> Option<&dyn MetaModel>;
}

pub trait MetaModel: Debug {
    fn name(&self) -> &str;

    // The section which implicitly surrounds the entire document.
    fn top_level_section_kind(&self) -> &dyn SectionKind;
}

// See https://github.com/rust-lang/rust/issues/106447.
macro_rules! dyn_ptr_eq {
    ($($trait:tt)+) => {
        impl PartialEq for &dyn $($trait)+ {
            fn eq(&self, other: &Self) -> bool {
                *self as *const dyn $($trait)+ as *const u8
                    == *other as *const dyn $($trait)+ as *const u8
            }
        }

        impl_mem_serializable_self!(&'static dyn $($trait)+);
    };
}

dyn_ptr_eq!(MetaModel);

pub trait SectionKind: Debug {
    fn parameterization(&self, paren: char) -> Option<&dyn SectionKind>;
    fn data_kind(&self) -> &dyn DataKind;
    fn param_kind(&self) -> &dyn ParamKind;
    fn subsection(&self, paren: char) -> Option<&dyn SectionKind>;
    fn notation_prefixes(&self) -> Option<NotationPrefixOptions>;
}

dyn_ptr_eq!(SectionKind);

pub struct NotationPrefixOptions {
    pub paren: char,
}

pub trait ParamKind: Debug {
    fn keyword_is_notation_delimiter(&self, keyword: &str) -> bool;
    fn identifier_is_notation_delimiter(&self, identifier: &str) -> bool;
    fn paren_is_notation_delimiter(&self, paren: char) -> bool;
}

dyn_ptr_eq!(ParamKind);

pub trait MappingKind: Debug {
    fn param_kind(&self) -> &dyn ParamKind;
}

dyn_ptr_eq!(MappingKind);

pub trait InfixMappingKind: MappingKind {
    fn binder_paren(&self) -> char;

    fn as_mapping_kind(&self) -> &dyn MappingKind;
}

dyn_ptr_eq!(InfixMappingKind);

pub trait DataKind: Debug {
    fn parameterization(&self, paren: char) -> Option<&dyn SectionKind>;
    fn special_data_kind(&self, paren: char) -> Option<&dyn DataKind>;
    fn prefix_mapping_kind(&self, identifier: &str) -> Option<&dyn MappingKind>;
    fn infix_mapping_kind(&self, identifier: &str) -> Option<&dyn InfixMappingKind>;
    fn object_kind(&self, paren: char) -> Option<&dyn ObjectKind>;
}

dyn_ptr_eq!(DataKind);

pub trait ObjectKind: Debug {
    fn separator(&self) -> char;

    fn parameterization(&self) -> &dyn SectionKind;
    fn param_data_kind(&self) -> &dyn DataKind;
    fn param_kind(&self) -> &dyn ParamKind;
    fn extra_part_kind(&self, extra_part_idx: usize) -> Option<&dyn SectionKind>;
}

dyn_ptr_eq!(ObjectKind);

#[cfg(test)]
pub mod testing {
    use std::fmt;

    use super::*;

    pub struct TestMetaModel;

    impl Debug for TestMetaModel {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("test")
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

    impl MappingKind for TestMetaModel {
        fn param_kind(&self) -> &dyn ParamKind {
            self
        }
    }

    impl InfixMappingKind for TestMetaModel {
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
                "λ" => Some(self),
                _ => None,
            }
        }

        fn infix_mapping_kind(&self, identifier: &str) -> Option<&dyn InfixMappingKind> {
            match identifier {
                "↦" => Some(self),
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

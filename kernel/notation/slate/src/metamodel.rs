use std::fmt::Debug;

use anyhow::Result;

pub trait MetaModelGetter {
    fn metamodel(&self, name: &str) -> Result<&dyn MetaModel>;
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
    };
}

dyn_ptr_eq!(MetaModel);

pub trait SectionKind: Debug {
    fn param_kind(&self) -> &dyn ParamKind;

    fn parenthesis_role(&self, start_paren: char) -> SectionParenthesisRole;
}

dyn_ptr_eq!(SectionKind);

pub enum SectionParenthesisRole<'a> {
    None,
    Parameterization(&'a dyn SectionKind),
    Section(&'a dyn SectionKind),
}

pub trait ParamKind: Debug {
    fn notation_kind(&self) -> Option<&dyn NotationKind>;
    fn data_kind(&self) -> Option<&dyn DataKind>;
}

dyn_ptr_eq!(ParamKind);

pub trait NotationKind: Debug {
    fn identifier_is_notation_delimiter(&self, identifier: &str) -> bool;
    fn paren_is_notation_delimiter(&self, start_paren: char) -> bool;

    fn mapping_kind(&self, identifier: &str) -> Option<&dyn MappingKind<dyn ParamKind>>;
}

dyn_ptr_eq!(NotationKind);

pub trait MappingKind<T: ?Sized>: Debug {
    fn notation(&self) -> MappingNotation;

    fn param_kind(&self) -> &dyn ParamKind;
    fn target_kind(&self) -> &T;
}

impl<T: ?Sized> PartialEq for &dyn MappingKind<T> {
    fn eq(&self, other: &Self) -> bool {
        *self as *const dyn MappingKind<T> as *const u8
            == *other as *const dyn MappingKind<T> as *const u8
    }
}

pub enum MappingNotation {
    Prefix,
    Infix { binder_paren: char },
}

pub trait DataKind: Debug {
    fn special_data_kind(&self, start_paren: char) -> Option<&dyn DataKind>;
    fn mapping_kind(&self, identifier: &str) -> Option<&dyn MappingKind<dyn DataKind>>;
    fn object_kind(&self, start_paren: char) -> Option<&dyn ObjectKind>;
}

dyn_ptr_eq!(DataKind);

pub trait ObjectKind: Debug {
    fn separator(&self) -> char;

    fn parameterization(&self) -> &dyn SectionKind;
    fn param_kind(&self) -> &dyn ParamKind;
    fn extra_section_kind(&self, extra_section_idx: u32) -> Option<&dyn SectionKind>;
}

dyn_ptr_eq!(ObjectKind);

#[cfg(test)]
pub mod test_helpers {
    use anyhow::anyhow;

    use super::*;

    pub struct TestMetaModel {
        pub is_infix_mapping: bool,
        pub opposite_mapping: Option<Box<TestMetaModel>>,
    }

    impl TestMetaModel {
        pub fn new() -> Self {
            TestMetaModel {
                is_infix_mapping: false,
                opposite_mapping: Some(Box::new(TestMetaModel {
                    is_infix_mapping: true,
                    opposite_mapping: Some(Box::new(TestMetaModel {
                        is_infix_mapping: false,
                        opposite_mapping: None,
                    })),
                })),
            }
        }

        fn get_mapping(&self, identifier: &str) -> Option<&Self> {
            match identifier {
                "λ" => {
                    if self.is_infix_mapping {
                        if let Some(prefix_mapping) = &self.opposite_mapping {
                            Some(prefix_mapping.as_ref())
                        } else {
                            None
                        }
                    } else {
                        Some(self)
                    }
                }
                "↦" => {
                    if self.is_infix_mapping {
                        Some(self)
                    } else {
                        if let Some(infix_mapping) = &self.opposite_mapping {
                            Some(infix_mapping.as_ref())
                        } else {
                            None
                        }
                    }
                }
                _ => None,
            }
        }
    }

    impl Debug for TestMetaModel {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.is_infix_mapping {
                f.write_str("infix")
            } else {
                f.write_str("test")
            }
        }
    }

    impl MetaModelGetter for TestMetaModel {
        fn metamodel(&self, name: &str) -> Result<&dyn MetaModel> {
            match name {
                "test" => Ok(self),
                name => Err(anyhow!("unknown metamodel \"{name}\"")),
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
        fn param_kind(&self) -> &dyn ParamKind {
            self
        }

        fn parenthesis_role(&self, start_paren: char) -> SectionParenthesisRole {
            match start_paren {
                '[' => SectionParenthesisRole::Parameterization(self),
                '{' => SectionParenthesisRole::Section(self),
                _ => SectionParenthesisRole::None,
            }
        }
    }

    impl ParamKind for TestMetaModel {
        fn notation_kind(&self) -> Option<&dyn NotationKind> {
            Some(self)
        }

        fn data_kind(&self) -> Option<&dyn DataKind> {
            Some(self)
        }
    }

    impl NotationKind for TestMetaModel {
        fn identifier_is_notation_delimiter(&self, identifier: &str) -> bool {
            identifier.starts_with(':')
        }

        fn paren_is_notation_delimiter(&self, start_paren: char) -> bool {
            start_paren == '⎿'
        }

        fn mapping_kind(&self, identifier: &str) -> Option<&dyn MappingKind<dyn ParamKind>> {
            Some(self.get_mapping(identifier)?)
        }
    }

    impl MappingKind<dyn ParamKind> for TestMetaModel {
        fn notation(&self) -> MappingNotation {
            if self.is_infix_mapping {
                MappingNotation::Infix { binder_paren: '(' }
            } else {
                MappingNotation::Prefix
            }
        }

        fn param_kind(&self) -> &dyn ParamKind {
            self
        }

        fn target_kind(&self) -> &(dyn ParamKind + 'static) {
            self
        }
    }

    impl MappingKind<dyn DataKind> for TestMetaModel {
        fn notation(&self) -> MappingNotation {
            if self.is_infix_mapping {
                MappingNotation::Infix { binder_paren: '(' }
            } else {
                MappingNotation::Prefix
            }
        }

        fn param_kind(&self) -> &dyn ParamKind {
            self
        }

        fn target_kind(&self) -> &(dyn DataKind + 'static) {
            self
        }
    }

    impl DataKind for TestMetaModel {
        fn special_data_kind(&self, _start_paren: char) -> Option<&dyn DataKind> {
            None
        }

        fn mapping_kind(&self, identifier: &str) -> Option<&dyn MappingKind<dyn DataKind>> {
            Some(self.get_mapping(identifier)?)
        }

        fn object_kind(&self, start_paren: char) -> Option<&dyn ObjectKind> {
            match start_paren {
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

        fn param_kind(&self) -> &dyn ParamKind {
            self
        }

        fn extra_section_kind(&self, _extra_section_idx: u32) -> Option<&dyn SectionKind> {
            Some(self)
        }
    }
}

use lang_def::parser::NameKindDesc;
use slate_lang_def::parser::metamodel::*;

#[derive(Debug)]
pub struct DTTMetaModel;

impl MetaModelPart for DTTMetaModel {
    fn id(&self) -> usize {
        0
    }
}

impl MetaModelGetter for DTTMetaModel {
    fn metamodel(&self, name: &str) -> Option<&dyn MetaModel> {
        match name {
            "dtt" => Some(self),
            _ => None,
        }
    }
}

impl MetaModel for DTTMetaModel {
    fn top_level_section_kind(&self) -> &dyn SectionKind {
        self
    }
}

impl SectionKind for DTTMetaModel {
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

impl ParamKind for DTTMetaModel {
    fn keyword_is_notation_delimiter(&self, keyword: &str) -> Option<NotationDelimiterDesc> {
        if matches!(keyword, "%Type" | "%Universe") {
            Some(NotationDelimiterDesc {
                kind: Some(NameKindDesc::Type),
                is_ref: false,
            })
        } else {
            None
        }
    }

    fn identifier_is_notation_delimiter(&self, ident: &str) -> Option<NotationDelimiterDesc> {
        match ident {
            ":" => Some(NotationDelimiterDesc {
                kind: Some(NameKindDesc::Value),
                is_ref: false,
            }),
            ":≡" => Some(NotationDelimiterDesc {
                kind: None,
                is_ref: false,
            }),
            "↦" => Some(NotationDelimiterDesc {
                kind: None,
                is_ref: true,
            }),
            _ => None,
        }
    }

    fn paren_is_notation_delimiter(&self, paren: char) -> Option<NotationDelimiterDesc> {
        if paren == '⎿' {
            Some(NotationDelimiterDesc {
                kind: None,
                is_ref: false,
            })
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct DTTPrefixMapping;

impl MetaModelPart for DTTPrefixMapping {
    fn id(&self) -> usize {
        0
    }
}

impl MappingKind for DTTPrefixMapping {
    fn param_kind(&self) -> &dyn ParamKind {
        &DTTMetaModel
    }
}

#[derive(Debug)]
pub struct DTTInfixMapping;

impl MetaModelPart for DTTInfixMapping {
    fn id(&self) -> usize {
        1
    }
}

impl MappingKind for DTTInfixMapping {
    fn param_kind(&self) -> &dyn ParamKind {
        &DTTMetaModel
    }
}

impl InfixMappingKind for DTTInfixMapping {
    fn binder_paren(&self) -> char {
        '('
    }

    fn as_mapping_kind(&self) -> &dyn MappingKind {
        self
    }
}

impl DataKind for DTTMetaModel {
    fn parameterization(&self, paren: char) -> Option<&dyn SectionKind> {
        match paren {
            '[' => Some(self),
            _ => None,
        }
    }

    fn special_data_kind(&self, _paren: char) -> Option<&dyn DataKind> {
        None
    }

    fn prefix_mapping_kind(&self, ident: &str) -> Option<&dyn MappingKind> {
        let mut chars = ident.chars();
        if let Some(ch) = chars.next() {
            if chars.next().is_none()
                && matches!(ch, '∀' | '∃' | '∄' | '∏' | '∐' | '∑' | '∫'..='∳' | '⨀'..='⨜')
            {
                return Some(&DTTPrefixMapping);
            }
        }
        None
    }

    fn infix_mapping_kind(&self, ident: &str) -> Option<&dyn InfixMappingKind> {
        match ident {
            "↦" => Some(&DTTInfixMapping),
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

impl ObjectKind for DTTMetaModel {
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
        if extra_part_idx == 0 {
            Some(self)
        } else {
            None
        }
    }
}

use lang_def::LanguageDefinition;
use parser::layer3_parameter_identifier::ParameterIdentifierConfig;

pub mod parser;

pub struct SlateLang;

impl LanguageDefinition for SlateLang {
    type ParserDesc = ParameterIdentifierConfig;
}

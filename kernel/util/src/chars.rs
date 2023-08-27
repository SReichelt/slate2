// TODO: delete

pub fn is_ascii_identifier_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || is_additional_identifier_char(c)
}

pub fn is_additional_identifier_char(c: char) -> bool {
    c == '_' || c == '\''
}

pub fn is_delimiter_char(c: char) -> bool {
    c.is_whitespace()
        || c.is_ascii_control()
        || is_basic_punctuation_char(c)
        || is_parenthesis_char(c)
        || c == '"'
        || c == '\\'
}

fn is_basic_punctuation_char(c: char) -> bool {
    matches!(c, '.' | ':' | ',' | ';')
}

fn is_parenthesis_char(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{'..='}' | '¦' | '«' | '»' | '⁅' | '⁆' | '‖'
                | '⌈'..='⌏' | '⌜'..='⌟' | '〈' | '〉' | '⟦'..='⟯' | '⦃'..='⦚' | '⧘'..='⧛' | '⧼' | '⧽' | '⸠'..='⸩'
                | '〈'..='】' | '〔'..='〛')
}

pub fn is_symbol_char(c: char) -> bool {
    c.is_ascii_punctuation()
        || matches!(c, '§' | '¬' | '¯'..='´' | '¶'..='¹' | '÷'
                       | '‐'..='₟' | '←'..='⏿' | '─'..='⯿' | '、'..='〿' | '⸀'..='⹿' | '🌀'..='🯿')
}

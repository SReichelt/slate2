pub fn is_keyword_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

pub fn is_delimiter_char(c: char) -> bool {
    c.is_whitespace()
        || c.is_ascii_control()
        || is_basic_punctuation_char(c)
        || is_parenthesis_char(c)
        || c == '`'
}

fn is_basic_punctuation_char(c: char) -> bool {
    matches!(c, '.' | ':' | ',' | ';')
}

pub fn is_group_connecting_char(c: char) -> bool {
    matches!(c, '_' | '\'' | '"')
}

pub fn is_symbol_char(c: char) -> bool {
    c.is_ascii_punctuation()
        || matches!(c, '§' | '¬' | '¯'..='´' | '¶'..='¹' | '÷'
                       | '‐'..='₟' | '←'..='⏿' | '─'..='⯿' | '、'..='〿' | '⸀'..='⹿' | '🌀'..='🯿')
}

fn is_parenthesis_char(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{'..='}' | '¦' | '«' | '»' | '⁅' | '⁆' | '‖'
                | '⌈'..='⌏' | '⌜'..='⌟' | '⎾'..='⏌' | '〈' | '〉' | '⟦'..='⟯' | '⦃'..='⦚' | '⧘'..='⧛' | '⧼' | '⧽'
                | '⸂'..='⸅' | '⸉' | '⸊' | '⸌' | '⸍' | '⸜' | '⸝' | '⸠'..='⸩' | '〈'..='】' | '〔'..='〛')
}

pub fn matching_closing_parenthesis(c: char) -> Option<char> {
    match c {
        '(' => Some(')'),
        '[' => Some(']'),
        '{' => Some('}'),
        '«' => Some('»'),
        '⁅' => Some('⁆'),
        '⌈' => Some('⌉'),
        '⌊' => Some('⌋'),
        '⌌' => Some('⌍'),
        '⌎' => Some('⌏'),
        '⌜' => Some('⌝'),
        '⌞' => Some('⌟'),
        '⎾' => Some('⎿'),
        '⏋' => Some('⏌'),
        '〈' => Some('〉'),
        '⟦' => Some('⟧'),
        '⟨' => Some('⟩'),
        '⟪' => Some('⟫'),
        '⟬' => Some('⟭'),
        '⟮' => Some('⟯'),
        '⦃' => Some('⦄'),
        '⦅' => Some('⦆'),
        '⦇' => Some('⦈'),
        '⦉' => Some('⦊'),
        '⦋' => Some('⦌'),
        '⦍' => Some('⦎'),
        '⦏' => Some('⦐'),
        '⦑' => Some('⦒'),
        '⦓' => Some('⦔'),
        '⦕' => Some('⦖'),
        '⦗' => Some('⦘'),
        '⧘' => Some('⧙'),
        '⧚' => Some('⧛'),
        '⧼' => Some('⧽'),
        '⸂' => Some('⸃'),
        '⸄' => Some('⸅'),
        '⸉' => Some('⸊'),
        '⸌' => Some('⸍'),
        '⸜' => Some('⸝'),
        '⸠' => Some('⸡'),
        '⸢' => Some('⸣'),
        '⸤' => Some('⸥'),
        '⸦' => Some('⸧'),
        '⸨' => Some('⸩'),
        '〈' => Some('〉'),
        '《' => Some('》'),
        '「' => Some('」'),
        '『' => Some('』'),
        '【' => Some('】'),
        '〔' => Some('〕'),
        '〖' => Some('〗'),
        '〘' => Some('〙'),
        '〚' => Some('〛'),
        _ => None,
    }
}

pub fn is_delimiter_char(c: char) -> bool {
    c.is_whitespace()
        || c.is_ascii_control()
        || is_basic_punctuation_char(c)
        || is_script_separator_char(c)
        || is_parenthesis_char(c)
        || c == '`'
}

pub fn is_pre_weakly_connecting_char(c: char) -> bool {
    is_basic_punctuation_char(c) || is_script_separator_char(c) || is_opening_parenthesis(c)
}

pub fn is_post_weakly_connecting_char(c: char) -> bool {
    is_basic_punctuation_char(c)
        || is_script_separator_char(c)
        || is_subscript_char(c)
        || is_superscript_char(c)
        || is_closing_parenthesis(c)
}

pub fn is_basic_punctuation_char(c: char) -> bool {
    matches!(c, '.' | ',' | ';')
}

pub fn is_script_separator_char(c: char) -> bool {
    matches!(c, '_' | '^')
}

pub fn is_prime_char(c: char) -> bool {
    matches!(c, '\'' | '"')
}

pub fn is_symbol_char(c: char) -> bool {
    c.is_ascii_punctuation()
        || matches!(c, '§' | '¬' | '¯'..='±' | '¶' | '·' | '¿' | '÷'
                       | '‐'..='⁞' | '←'..='⏿' | '─'..='⯿' | '、'..='〿' | '⸀'..='⹿' | '🌀'..='🯿')
}

pub fn is_subscript_char(c: char) -> bool {
    matches!(c, '₀'..='₟')
}

pub fn is_superscript_char(c: char) -> bool {
    matches!(c, 'ª' | '²' | '³' | '¹' | 'º' | '⁰'..='ⁿ')
}

pub fn is_parenthesis_char(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{'..='}' | '¦' | '«' | '»' | '‹' | '›' | '⁅' | '⁆' | '‖'
                | '⌈'..='⌏' | '⌜'..='⌟' | '⎾'..='⏌' | '〈' | '〉' | '⟦'..='⟯' | '⦃'..='⦚' | '⧘'..='⧛' | '⧼' | '⧽'
                | '⸂'..='⸅' | '⸉' | '⸊' | '⸌' | '⸍' | '⸜' | '⸝' | '⸠'..='⸩' | '〈'..='】' | '〔'..='〛')
}

macro_rules! parens {
    ($(($opening:expr, $closing:expr)),* $(,)?) => {
        pub fn is_opening_parenthesis(c: char) -> bool {
            match c {
                $($opening => $opening != $closing,)*
                _ => false
            }
        }

        pub fn is_closing_parenthesis(c: char) -> bool {
            match c {
                $($closing => $opening != $closing,)*
                _ => false
            }
        }

        pub fn matching_closing_parenthesis(c: char) -> Option<char> {
            match c {
                $($opening => Some($closing),)*
                _ => None
            }
        }
    };
}

parens![
    ('(', ')'),
    ('[', ']'),
    ('{', '}'),
    ('|', '|'),
    ('¦', '¦'),
    ('«', '»'),
    ('‹', '›'),
    ('⁅', '⁆'),
    ('‖', '‖'),
    ('⌈', '⌉'),
    ('⌊', '⌋'),
    ('⌌', '⌍'),
    ('⌎', '⌏'),
    ('⌜', '⌝'),
    ('⌞', '⌟'),
    ('⎾', '⏋'),
    ('⎿', '⏌'),
    ('〈', '〉'),
    ('⟦', '⟧'),
    ('⟨', '⟩'),
    ('⟪', '⟫'),
    ('⟬', '⟭'),
    ('⟮', '⟯'),
    ('⦃', '⦄'),
    ('⦅', '⦆'),
    ('⦇', '⦈'),
    ('⦉', '⦊'),
    ('⦋', '⦌'),
    ('⦍', '⦎'),
    ('⦏', '⦐'),
    ('⦑', '⦒'),
    ('⦓', '⦔'),
    ('⦕', '⦖'),
    ('⦗', '⦘'),
    ('⧘', '⧙'),
    ('⧚', '⧛'),
    ('⧼', '⧽'),
    ('⸂', '⸃'),
    ('⸄', '⸅'),
    ('⸉', '⸊'),
    ('⸌', '⸍'),
    ('⸜', '⸝'),
    ('⸠', '⸡'),
    ('⸢', '⸣'),
    ('⸤', '⸥'),
    ('⸦', '⸧'),
    ('⸨', '⸩'),
    ('〈', '〉'),
    ('《', '》'),
    ('「', '」'),
    ('『', '』'),
    ('【', '】'),
    ('〔', '〕'),
    ('〖', '〗'),
    ('〘', '〙'),
    ('〚', '〛'),
];

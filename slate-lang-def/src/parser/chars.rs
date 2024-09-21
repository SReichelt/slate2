pub fn is_delimiter_char(ch: char) -> bool {
    ch.is_whitespace()
        || ch.is_ascii_control()
        || is_basic_punctuation_char(ch)
        || is_script_separator_char(ch)
        || is_parenthesis_char(ch)
        || ch == '`'
}

pub fn is_pre_weakly_connecting_char(ch: char) -> bool {
    is_basic_punctuation_char(ch) || is_script_separator_char(ch) || is_opening_parenthesis(ch)
}

pub fn is_post_weakly_connecting_char(ch: char) -> bool {
    is_basic_punctuation_char(ch)
        || is_script_separator_char(ch)
        || is_subscript_char(ch)
        || is_superscript_char(ch)
        || is_closing_parenthesis(ch)
}

pub fn is_basic_punctuation_char(ch: char) -> bool {
    matches!(ch, '.' | ',' | ';')
}

pub fn is_script_separator_char(ch: char) -> bool {
    matches!(ch, '_' | '^')
}

pub fn is_prime_char(ch: char) -> bool {
    matches!(ch, '\'' | '"')
}

pub fn is_symbol_char(ch: char) -> bool {
    ch.is_ascii_punctuation()
        || matches!(ch, '§' | '¬' | '¯'..='±' | '¶' | '·' | '¿' | '÷'
                        | '‐'..='⁞' | '←'..='⏿' | '─'..='⯿' | '、'..='〿' | '⸀'..='⹿' | '🌀'..='🯿')
}

pub fn is_subscript_char(ch: char) -> bool {
    matches!(ch, '₀'..='₟')
}

pub fn is_superscript_char(ch: char) -> bool {
    matches!(ch, 'ª' | '²' | '³' | '¹' | 'º' | '⁰'..='ⁿ')
}

pub fn is_parenthesis_char(ch: char) -> bool {
    matches!(ch, '(' | ')' | '[' | ']' | '{'..='}' | '¦' | '«' | '»' | '‹' | '›' | '⁅' | '⁆' | '‖'
                 | '⌈'..='⌏' | '⌜'..='⌟' | '⎾'..='⏌' | '〈' | '〉' | '⟦'..='⟯' | '⦃'..='⦚' | '⧘'..='⧛' | '⧼' | '⧽'
                 | '⸂'..='⸅' | '⸉' | '⸊' | '⸌' | '⸍' | '⸜' | '⸝' | '⸠'..='⸩' | '〈'..='】' | '〔'..='〛')
}

macro_rules! parens {
    ($(($opening:expr, $closing:expr)),* $(,)?) => {
        pub fn is_opening_parenthesis(ch: char) -> bool {
            match ch {
                $($opening => $opening != $closing,)*
                _ => false
            }
        }

        pub fn is_closing_parenthesis(ch: char) -> bool {
            match ch {
                $($closing => $opening != $closing,)*
                _ => false
            }
        }

        pub fn matching_closing_parenthesis(ch: char) -> Option<char> {
            match ch {
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

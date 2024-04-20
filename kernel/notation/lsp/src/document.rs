use std::borrow::Cow;

use tower_lsp::{
    jsonrpc::{Error, ErrorCode, Result},
    lsp_types::{Range, TextEdit},
};

use slate_kernel_notation_generic::{event_sequence::*, event_source::*};
use slate_kernel_notation_text::{text_rope::*, type_list};

#[derive(Debug)]
pub struct Document {
    valid: bool,
    position_encoding: PositionEncoding,
    text: TextBuffer,
}

impl Document {
    pub fn new(position_encoding: PositionEncoding, text: &str) -> Self {
        let input = Self::get_initial_input(text);

        if let Ok(text) = TextBuffer::from_input(input) {
            Document {
                valid: true,
                position_encoding,
                text,
            }
        } else {
            Document {
                valid: false,
                position_encoding,
                text: TextBuffer::new(),
            }
        }
    }

    pub fn replace(&mut self, range: &Range, new_text: &str) -> Result<()> {
        if !self.valid {
            return Ok(());
        }

        let text_range = self.get_text_range(range)?;
        let input = self.get_modification_input(&text_range, new_text);

        // TODO: update/invalidate parse memory
        let Ok(_) = self
            .text
            .replace(Some(text_range.start)..Some(text_range.end), input)
        else {
            self.valid = false;
            self.text = TextBuffer::new();
            return Ok(());
        };

        Ok(())
    }

    pub fn edit(&mut self, text_edit: &TextEdit) -> Result<()> {
        self.replace(&text_edit.range, &text_edit.new_text)
    }

    fn get_text_range(&self, range: &Range) -> Result<TextRange> {
        if self.text.total_chunk_count() == 0 {
            return Ok(Default::default()..Default::default());
        }

        let (start0, (start1, (start2, (start3, start_chunk)))) =
            self.text.chunk_str(range.start.line as usize);
        let start_idx = self
            .position_encoding
            .lsp_to_rust(start_chunk, range.start.character)?;
        let start_marker = LeafPosition::from_usize(start_idx);

        if range.end.line == range.start.line && range.end.character >= range.start.character {
            // Optimize by continuing from start_idx.
            let end_offset = self.position_encoding.lsp_to_rust(
                &start_chunk[start_idx..],
                range.end.character - range.start.character,
            )?;
            let end_marker = LeafPosition::from_usize(start_idx + end_offset);
            Ok((start0, (start1, (start2, (start3, start_marker))))
                ..(start0, (start1, (start2, (start3, end_marker)))))
        } else {
            let (end0, (end1, (end2, (end3, end_chunk)))) =
                self.text.chunk_str(range.end.line as usize);
            let end_idx = self
                .position_encoding
                .lsp_to_rust(end_chunk, range.end.character)?;
            let end_marker = LeafPosition::from_usize(end_idx);
            Ok((start0, (start1, (start2, (start3, start_marker))))
                ..(end0, (end1, (end2, (end3, end_marker)))))
        }
    }

    fn get_initial_input<'a>(text: &'a str) -> TextInput<'a> {
        let lines = Self::split_lines(text);
        <TextInput as TextRopeInput<'a, TextBufferShape>>::balanced(&lines)
    }

    fn get_modification_input<'a>(
        &self,
        text_range: &TextRange,
        new_text: &'a str,
    ) -> TextInput<'a> {
        todo!()
    }

    fn split_lines(mut text: &str) -> Vec<&str> {
        let mut result = Vec::new();
        while let Some(pos) = text.find(&['\r', '\n']) {
            let split_pos = if text[pos..].starts_with("\r\n") {
                pos + 2
            } else {
                pos + 1
            };
            let (line, rest) = text.split_at(split_pos);
            result.push(line);
            text = rest;
        }
        result.push(text);
        result
    }

    // TODO: add method to update invalidated parse memory and query semantic tokens
}

#[derive(Clone, Copy, Debug)]
pub enum PositionEncoding {
    UTF8,
    UTF16,
    UTF32,
}

impl PositionEncoding {
    fn lsp_to_rust(self, s: &str, mut lsp_pos: u32) -> Result<usize> {
        match self {
            PositionEncoding::UTF8 => {
                let idx = lsp_pos as usize;
                if !s.is_char_boundary(idx) {
                    return Err(Error {
                        code: ErrorCode::InvalidParams,
                        message: Cow::Borrowed("UTF-8 index not at character boundary"),
                        data: None,
                    });
                }
                Ok(idx)
            }
            PositionEncoding::UTF16 => {
                let mut buf = [0; 2];
                for (idx, ch) in s.char_indices() {
                    if lsp_pos == 0 {
                        return Ok(idx);
                    }
                    let char_len = ch.encode_utf16(&mut buf).len() as u32;
                    if lsp_pos < char_len {
                        return Err(Error {
                            code: ErrorCode::InvalidParams,
                            message: Cow::Borrowed("UTF-16 index not at character boundary"),
                            data: None,
                        });
                    }
                    lsp_pos -= char_len;
                }
                if lsp_pos == 0 {
                    Ok(s.len())
                } else {
                    Err(Error {
                        code: ErrorCode::InvalidParams,
                        message: Cow::Borrowed("UTF-16 index beyond end of string"),
                        data: None,
                    })
                }
            }
            PositionEncoding::UTF32 => {
                for (idx, _) in s.char_indices() {
                    if lsp_pos == 0 {
                        return Ok(idx);
                    }
                    lsp_pos -= 1;
                }
                if lsp_pos == 0 {
                    Ok(s.len())
                } else {
                    Err(Error {
                        code: ErrorCode::InvalidParams,
                        message: Cow::Borrowed("UTF-32 index beyond end of string"),
                        data: None,
                    })
                }
            }
        }
    }

    fn rust_to_lsp(self, s: &str, idx: usize) -> u32 {
        match self {
            PositionEncoding::UTF8 => idx as u32,
            PositionEncoding::UTF16 => {
                let mut lsp_pos = 0;
                let mut buf = [0; 2];
                for ch in s[..idx].chars() {
                    lsp_pos += ch.encode_utf16(&mut buf).len() as u32;
                }
                lsp_pos
            }
            PositionEncoding::UTF32 => s[..idx].chars().count() as u32,
        }
    }
}

#[derive(Default, Clone, Debug)]
struct LineParseMemory {
    range_events: Vec<RangeClassEvent>,
}

type TextBufferShape = type_list![u8, u8, u8, u8];
type TextBuffer = TextRope<TextBufferShape, type_list![]>;
type TextPosition = <TextBufferShape as TextRopeShape>::Position;
type TextRange = std::ops::Range<TextPosition>;
type TextInput<'a> = <TextBufferShape as TextRopeShape>::Input<'a>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lsp_to_rust_utf8() {
        let s = "a𐐀b"; // example from LSP specification
        assert_eq!(s.len(), 6);
        assert_eq!(PositionEncoding::UTF8.lsp_to_rust(s, 0), Ok(0));
        assert_eq!(PositionEncoding::UTF8.lsp_to_rust(s, 1), Ok(1));
        assert!(PositionEncoding::UTF8.lsp_to_rust(s, 2).is_err());
        assert!(PositionEncoding::UTF8.lsp_to_rust(s, 3).is_err());
        assert!(PositionEncoding::UTF8.lsp_to_rust(s, 4).is_err());
        assert_eq!(PositionEncoding::UTF8.lsp_to_rust(s, 5), Ok(5));
        assert_eq!(PositionEncoding::UTF8.lsp_to_rust(s, 6), Ok(6));
        assert!(PositionEncoding::UTF8.lsp_to_rust(s, 7).is_err());
    }

    #[test]
    fn lsp_to_rust_utf16() {
        let s = "a𐐀b"; // example from LSP specification
        assert_eq!(s.len(), 6);
        assert_eq!(PositionEncoding::UTF16.lsp_to_rust(s, 0), Ok(0));
        assert_eq!(PositionEncoding::UTF16.lsp_to_rust(s, 1), Ok(1));
        assert!(PositionEncoding::UTF16.lsp_to_rust(s, 2).is_err());
        assert_eq!(PositionEncoding::UTF16.lsp_to_rust(s, 3), Ok(5));
        assert_eq!(PositionEncoding::UTF16.lsp_to_rust(s, 4), Ok(6));
        assert!(PositionEncoding::UTF16.lsp_to_rust(s, 5).is_err());
    }

    #[test]
    fn lsp_to_rust_utf32() {
        let s = "a𐐀b"; // example from LSP specification
        assert_eq!(s.len(), 6);
        assert_eq!(PositionEncoding::UTF32.lsp_to_rust(s, 0), Ok(0));
        assert_eq!(PositionEncoding::UTF32.lsp_to_rust(s, 1), Ok(1));
        assert_eq!(PositionEncoding::UTF32.lsp_to_rust(s, 2), Ok(5));
        assert_eq!(PositionEncoding::UTF32.lsp_to_rust(s, 3), Ok(6));
        assert!(PositionEncoding::UTF32.lsp_to_rust(s, 4).is_err());
    }

    #[test]
    fn rust_to_lsp_utf16() {
        let s = "a𐐀b"; // example from LSP specification
        assert_eq!(s.len(), 6);
        assert_eq!(PositionEncoding::UTF16.rust_to_lsp(s, 0), 0);
        assert_eq!(PositionEncoding::UTF16.rust_to_lsp(s, 1), 1);
        assert_eq!(PositionEncoding::UTF16.rust_to_lsp(s, 5), 3);
        assert_eq!(PositionEncoding::UTF16.rust_to_lsp(s, 6), 4);
    }

    #[test]
    fn rust_to_lsp_utf32() {
        let s = "a𐐀b"; // example from LSP specification
        assert_eq!(s.len(), 6);
        assert_eq!(PositionEncoding::UTF32.rust_to_lsp(s, 0), 0);
        assert_eq!(PositionEncoding::UTF32.rust_to_lsp(s, 1), 1);
        assert_eq!(PositionEncoding::UTF32.rust_to_lsp(s, 5), 2);
        assert_eq!(PositionEncoding::UTF32.rust_to_lsp(s, 6), 3);
    }

    #[test]
    fn split_lines() {
        assert_eq!(Document::split_lines(""), &[""]);
        assert_eq!(Document::split_lines("a"), &["a"]);
        assert_eq!(Document::split_lines("\n"), &["\n", ""]);
        assert_eq!(Document::split_lines("\r"), &["\r", ""]);
        assert_eq!(Document::split_lines("\r\n"), &["\r\n", ""]);
        assert_eq!(Document::split_lines("\n\n"), &["\n", "\n", ""]);
        assert_eq!(Document::split_lines("\r\r"), &["\r", "\r", ""]);
        assert_eq!(Document::split_lines("\n\r"), &["\n", "\r", ""]);
        assert_eq!(
            Document::split_lines("abc\ndef\n\nghi"),
            &["abc\n", "def\n", "\n", "ghi"]
        );
        assert_eq!(
            Document::split_lines("abc\r\ndef\r\n\r\nghi"),
            &["abc\r\n", "def\r\n", "\r\n", "ghi"]
        );
    }
}

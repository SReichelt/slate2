use std::{borrow::Cow, ops::Range};

use nonminmax::NonMaxU32;

use crate::{char::*, event::*};

type Marker = NonMaxU32;

fn pack_marker(idx: usize) -> Marker {
    Marker::new(idx as u32).unwrap()
}

fn unpack_marker(marker: &Marker) -> usize {
    marker.get() as usize
}

fn unpack_marker_range(range: Range<&Marker>) -> Range<usize> {
    let start = unpack_marker(range.start);
    let end = unpack_marker(range.end);
    start..end
}

impl<'a> CharEventOps<'a, Marker> for &'a str {
    fn slice(&self, range: Range<&Marker>) -> Cow<'a, str> {
        Cow::Borrowed(&self[unpack_marker_range(range)])
    }
}

pub struct CharSliceEventSource<'a, DiagSink: CharSliceDiagnosticSink> {
    input: &'a str,
    diag_sink: &'a DiagSink,
}

impl<'a, DiagSink: CharSliceDiagnosticSink> CharSliceEventSource<'a, DiagSink> {
    pub fn new(input: &'a str, diag_sink: &'a DiagSink) -> Result<Self, Message> {
        let max = u32::MAX as usize;
        if input.len() > max {
            Err(format!("input larger than {max} bytes not supported"))
        } else {
            Ok(CharSliceEventSource { input, diag_sink })
        }
    }

    pub fn run<Sink: EventSink<'a, Ev = char>>(&'a self, sink: Sink) {
        let pass = sink.start(self, &self.input);
        self.run_pass(pass)
    }

    fn run_pass<Pass: EventSinkPass<Ev = char, Marker = Marker>>(&'a self, pass: Pass) {
        let mut state = pass.new_state();
        let mut chars = self.input.char_indices();
        while let Some((idx, c)) = chars.next() {
            let start_marker = pack_marker(idx);
            let end_marker = pack_marker(chars.offset());
            pass.event(&mut state, c, &start_marker..&end_marker);
        }
        let end_marker = pack_marker(chars.offset());
        if let Some(next_pass) = pass.next_pass(state, &end_marker) {
            self.run_pass(next_pass)
        }
    }
}

impl<'a, DiagSink: CharSliceDiagnosticSink> Clone for CharSliceEventSource<'a, DiagSink> {
    fn clone(&self) -> Self {
        Self {
            input: self.input,
            diag_sink: self.diag_sink,
        }
    }
}

impl<'a, DiagSink: CharSliceDiagnosticSink> EventSource for CharSliceEventSource<'a, DiagSink> {
    type Marker = Marker;

    fn diagnostic(&self, range: Range<&Self::Marker>, severity: Severity, msg: Message) {
        self.diag_sink
            .diagnostic(unpack_marker_range(range), severity, msg)
    }
}

pub trait CharSliceDiagnosticSink {
    fn diagnostic(&self, range: Range<usize>, severity: Severity, msg: Message);
}

pub mod test_helpers {
    use std::cell::RefCell;

    use super::*;

    #[derive(Clone, PartialEq, Debug)]
    pub struct TestDiagnosticMessage {
        pub range_text: String,
        pub severity: Severity,
        pub msg: Message,
    }

    pub struct DiagnosticsRecorder<'a> {
        input: &'a str,
        diagnostics: RefCell<Vec<TestDiagnosticMessage>>,
    }

    impl<'a> DiagnosticsRecorder<'a> {
        pub fn new(input: &'a str) -> Self {
            DiagnosticsRecorder {
                input,
                diagnostics: RefCell::new(Vec::new()),
            }
        }

        pub fn diagnostics(self) -> Vec<TestDiagnosticMessage> {
            self.diagnostics.into_inner()
        }
    }

    impl CharSliceDiagnosticSink for DiagnosticsRecorder<'_> {
        fn diagnostic(&self, range: Range<usize>, severity: Severity, msg: Message) {
            self.diagnostics.borrow_mut().push(TestDiagnosticMessage {
                range_text: self.input[range].into(),
                severity,
                msg,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::char::test_helpers::*;

    use super::*;

    #[test]
    fn single_pass() -> Result<(), Message> {
        test_char_recording("test", 1)
    }

    #[test]
    fn three_passes() -> Result<(), Message> {
        test_char_recording("test", 3)
    }

    fn test_char_recording(input: &str, mut passes: u32) -> Result<(), Message> {
        let source = CharSliceEventSource::new(input, &DummyDiagnosticsSink)?;
        source.run(CharRecordingSink {
            input,
            passes: &mut passes,
        });
        assert_eq!(passes, 0);
        Ok(())
    }

    #[test]
    fn slicing() -> Result<(), Message> {
        let source = CharSliceEventSource::new("abc<def>ghi", &DummyDiagnosticsSink)?;
        let mut result = String::new();
        source.run(SlicingSink {
            start_char: '<',
            end_char: '>',
            result: &mut result,
        });
        assert_eq!(result, "<def>");
        Ok(())
    }

    struct DummyDiagnosticsSink;

    impl CharSliceDiagnosticSink for DummyDiagnosticsSink {
        fn diagnostic(&self, _range: Range<usize>, _severity: Severity, msg: Message) {
            panic!("unexpected diagnostic: {msg}")
        }
    }
}

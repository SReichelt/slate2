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
        let special_ops: &'a dyn CharEventOps<'a, Marker> = &self.input;
        let pass = sink.start(EventSourceWithOps(self.clone(), special_ops));
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

    fn range_event(&self, event: RangeClassEvent, marker: &Self::Marker) {
        self.diag_sink.range_event(event, unpack_marker(marker))
    }
}

pub trait CharSliceDiagnosticSink {
    fn diagnostic(&self, range: Range<usize>, severity: Severity, msg: Message);

    fn range_event(&self, event: RangeClassEvent, marker: usize);
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
        range_events: RefCell<Vec<(RangeClassEvent, usize)>>,
    }

    impl<'a> DiagnosticsRecorder<'a> {
        pub fn new(input: &'a str) -> Self {
            DiagnosticsRecorder {
                input,
                diagnostics: RefCell::new(Vec::new()),
                range_events: RefCell::new(Vec::new()),
            }
        }

        pub fn results(self) -> (Vec<TestDiagnosticMessage>, Vec<(RangeClassEvent, usize)>) {
            let diagnostics = self.diagnostics.into_inner();

            let mut range_events = self.range_events.into_inner();
            let mut cur_ranges = Vec::new();
            for idx in 0..range_events.len() {
                let (event, _) = &mut range_events[idx];
                match event {
                    RangeClassEvent::Start(class) => cur_ranges.push(*class),
                    RangeClassEvent::End(class) => {
                        if let Some(expected_class) = cur_ranges.pop() {
                            if expected_class != *class {
                                for search_idx in (idx + 1)..range_events.len() {
                                    let (search_event, _) = range_events[search_idx];
                                    if search_event == RangeClassEvent::End(expected_class) {
                                        for swap_idx in (idx..search_idx).rev() {
                                            range_events.swap(swap_idx, swap_idx + 1);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            (diagnostics, range_events)
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

        fn range_event(&self, event: RangeClassEvent, marker: usize) {
            let mut range_events = self.range_events.borrow_mut();
            let mut insert_idx = range_events.len();
            while insert_idx > 0 {
                let (prev_event, prev_marker) = &range_events[insert_idx - 1];
                if *prev_marker < marker
                    || (*prev_marker == marker && !event.shift_before(prev_event))
                {
                    break;
                }
                insert_idx -= 1;
            }
            range_events.insert(insert_idx, (event, marker));
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

        fn range_event(&self, _event: RangeClassEvent, _marker: usize) {}
    }
}

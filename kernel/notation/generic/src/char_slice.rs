use std::{borrow::Cow, ops::Range};

use nonminmax::NonMaxU32;

use crate::{char::*, event::*, event_sequence::*, event_source::*};

pub(crate) type Marker = NonMaxU32;
pub(crate) const MAX_LEN: usize = (u32::MAX - 1) as usize;

pub(crate) fn pack_marker(idx: usize) -> Marker {
    Marker::new(idx as u32).unwrap()
}

pub(crate) fn unpack_marker(marker: &Marker) -> usize {
    marker.get() as usize
}

pub(crate) fn unpack_marker_range(range: Range<&Marker>) -> Range<usize> {
    let start = unpack_marker(range.start);
    let end = unpack_marker(range.end);
    start..end
}

#[derive(Clone, Copy)]
pub struct CharSlice<'a> {
    input: &'a str,
}

impl<'a> CharSlice<'a> {
    pub fn new(input: &'a str) -> Result<Self, Message> {
        if input.len() > MAX_LEN {
            Err(format!("input larger than {MAX_LEN} bytes not supported"))
        } else {
            Ok(CharSlice { input })
        }
    }

    pub fn input(&self) -> &'a str {
        self.input
    }
}

impl<'a> EventSequence<'a> for CharSlice<'a> {
    type Ev = char;
    type Marker = Marker;

    fn for_each(&self, mut f: impl FnMut(Self::Ev, Range<&Self::Marker>)) -> Self::Marker {
        let mut chars = self.input.char_indices();
        while let Some((idx, c)) = chars.next() {
            let start_marker = pack_marker(idx);
            let end_marker = pack_marker(chars.offset());
            f(c, &start_marker..&end_marker);
        }
        pack_marker(chars.offset())
    }

    fn special_ops(&'a self) -> <Self::Ev as Event>::SpecialOps<'a, Self::Marker> {
        self
    }

    fn start_marker() -> Self::Marker {
        Marker::new(0).unwrap()
    }
}

impl<'a> CharEventOps<'a, Marker> for CharSlice<'a> {
    fn slice(&'a self, range: Range<&Marker>) -> Cow<'a, str> {
        Cow::Borrowed(&self.input[unpack_marker_range(range)])
    }
}

pub trait CharSliceDiagnosticSink {
    fn diagnostic(&self, range: Range<usize>, severity: Severity, msg: Message);

    fn range_event(&self, event: RangeClassEvent, marker: usize);
}

impl<DiagSink: CharSliceDiagnosticSink> EventSource for &DiagSink {
    type Marker = Marker;

    fn diagnostic(&self, range: Range<&Self::Marker>, severity: Severity, msg: Message) {
        CharSliceDiagnosticSink::diagnostic(*self, unpack_marker_range(range), severity, msg)
    }

    fn range_event(&self, event: RangeClassEvent, marker: &Self::Marker) {
        CharSliceDiagnosticSink::range_event(*self, event, unpack_marker(marker))
    }
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

    pub struct TestCharSource<'a> {
        sequence: CharSlice<'a>,
        diagnostics: RefCell<Vec<TestDiagnosticMessage>>,
        range_events: RefCell<Vec<(RangeClassEvent, usize)>>,
    }

    impl<'a> TestCharSource<'a> {
        pub fn new(input: &'a str) -> Result<Self, Message> {
            Ok(TestCharSource {
                sequence: CharSlice::new(input)?,
                diagnostics: RefCell::new(Vec::new()),
                range_events: RefCell::new(Vec::new()),
            })
        }

        pub fn run<Sink: EventSink<'a, Ev = char>>(&'a self, sink: Sink) {
            self.sequence.run(self, sink)
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

    impl CharSliceDiagnosticSink for TestCharSource<'_> {
        fn diagnostic(&self, range: Range<usize>, severity: Severity, msg: Message) {
            self.diagnostics.borrow_mut().push(TestDiagnosticMessage {
                range_text: self.sequence.input()[range].into(),
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
        let sequence = CharSlice::new(input)?;
        sequence.run(
            &DummyDiagnosticsSink,
            CharRecordingSink {
                input,
                passes: &mut passes,
            },
        );
        assert_eq!(passes, 0);
        Ok(())
    }

    #[test]
    fn slicing() -> Result<(), Message> {
        let sequence = CharSlice::new("abc<def>ghi")?;
        let mut result = String::new();
        sequence.run(
            &DummyDiagnosticsSink,
            SlicingSink {
                start_char: '<',
                end_char: '>',
                result: &mut result,
            },
        );
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

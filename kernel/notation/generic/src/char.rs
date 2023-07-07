use std::{borrow::Cow, ops::Range};

use crate::event::*;

impl Event for char {
    type SpecialOps<'a, Marker: 'a> = &'a dyn CharEventOps<'a, Marker>;
}

pub trait CharEventOps<'a, Marker> {
    fn slice(&self, range: Range<&Marker>) -> Cow<'a, str>;
}

pub mod test_helpers {
    use std::ops::Range;

    use super::*;

    pub struct CharRecordingSink<'a> {
        pub input: &'a str,
        pub passes: &'a mut u32,
    }

    impl<'a> SimpleEventSink for CharRecordingSink<'a> {
        type Ev = char;
        type State = String;

        fn new_state(&self) -> Self::State {
            String::new()
        }

        fn event(&self, state: &mut Self::State, event: char) {
            state.push(event);
        }

        fn next_pass(self, state: Self::State) -> Option<Self> {
            assert_eq!(state, self.input);
            *self.passes -= 1;
            if *self.passes > 0 {
                Some(self)
            } else {
                None
            }
        }
    }

    pub struct SlicingSink<'a> {
        pub start_char: char,
        pub end_char: char,
        pub result: &'a mut String,
    }

    impl<'a> EventSink<'a> for SlicingSink<'a> {
        type Ev = char;
        type Pass<Src: EventSource + 'a> = SlicingSinkPass<'a, Src::Marker>;

        fn start<Src: EventSource + 'a>(
            self,
            _source: Src,
            special_ops: <Self::Ev as Event>::SpecialOps<'a, Src::Marker>,
        ) -> Self::Pass<Src> {
            SlicingSinkPass {
                sink: self,
                special_ops,
            }
        }
    }

    pub struct SlicingSinkPass<'a, Marker: 'a> {
        pub sink: SlicingSink<'a>,
        pub special_ops: <char as Event>::SpecialOps<'a, Marker>,
    }

    impl<'a, Marker: Clone + PartialEq> EventSinkPass for SlicingSinkPass<'a, Marker> {
        type Ev = char;
        type Marker = Marker;
        type State = Range<Option<Marker>>;
        type NextPass = Self;

        fn new_state(&self) -> Self::State {
            None..None
        }

        fn event(&self, state: &mut Self::State, event: char, range: Range<&Self::Marker>) {
            if event == self.sink.start_char {
                state.start = Some(range.start.clone());
            }
            if event == self.sink.end_char {
                state.end = Some(range.end.clone());
            }
        }

        fn next_pass(
            self,
            state: Self::State,
            _end_marker: &Self::Marker,
        ) -> Option<Self::NextPass> {
            *self.sink.result = self
                .special_ops
                .slice(&state.start.unwrap()..&state.end.unwrap())
                .into();
            None
        }
    }
}

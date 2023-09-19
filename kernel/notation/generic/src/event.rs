//! When iterating over characters in a file, or over tokens, or over more complex structures, we
//! consider each character/token/etc. as an "event". An "event sink" receives such events and
//! mutates its state accordingly.
//!
//! The entity sending the events may clone the state at any time, to restart from that state later
//! instead of replaying events.
//!
//! The event sink specifies how many passes are required. The same events must be sent in each
//! pass.

// Note: Code in this package is weirdly sensitive to the distinction between type parameters and
// associated types. Even though both are interchangeable in many cases, Rust currently has two
// constraints that dictate where to use which:
// * If we want to provide a "blanket implementation" for a trait with parameters (see
//   `EventSinkState`), then the parameters cannot be associated types.
// * If we want to use a trait in a struct parameter, then usually (but not always) it cannot have
//   parameters, as that leads to "unused type parameter" errors if we want to parameterize over it
//   in the struct as well. (Sometimes we can work around this using `PhantomData`.)
// In the end, we decided to use associated types everywhere, as blanket implementations were not
// needed.

use std::{marker::PhantomData, ops::Range};

pub trait Event {
    type SpecialOps<'a, Marker: 'a>: Clone = ();
}

pub trait EventSink<'a> {
    type Ev: Event;

    // An event sink is additionally split between `EventSink` and `EventSinkPass`, where
    // the state managed by `EventSinkPass` may include markers whose type depends on a concrete
    // `EventSource` type.
    type Pass<Src: EventSource + 'a>: EventSinkPass<
        Ev = Self::Ev,
        Marker = Src::Marker,
        NextPass = Self::Pass<Src>,
    >;

    fn start<Src: EventSource + 'a>(
        self,
        source: EventSourceWithOps<'a, Self::Ev, Src>,
    ) -> Self::Pass<Src>;
}

pub trait EventSinkPass: Sized {
    type Ev: Event;
    type Marker: Clone + PartialEq;
    type State: Clone + PartialEq;

    // We want every pass to have its own type, but in `EventSink` we require `NextPass` to be
    // `Self` to avoid combinatorial explosion in multi-pass event translators. Whenever we do have
    // different types, we can use `EventSinkPassCombinator` to dispatch between them.
    type NextPass: EventSinkPass<Ev = Self::Ev, Marker = Self::Marker> = Self;

    fn new_state(&self) -> Self::State;
    fn event(&self, state: &mut Self::State, event: Self::Ev, range: Range<&Self::Marker>);
    fn next_pass(self, state: Self::State, end_marker: &Self::Marker) -> Option<Self::NextPass>;
}

// Helper to combine two types that implement `EventSinkPass` into one. Can be used recursively in
// `Snd`.
pub enum EventSinkPassCombinator<
    Fst: EventSinkPass<NextPass = Snd>,
    Snd: EventSinkPass<Ev = Fst::Ev, Marker = Fst::Marker, NextPass = Snd>,
> {
    First(Fst),
    Next(Snd),
}

impl<
        Fst: EventSinkPass<NextPass = Snd>,
        Snd: EventSinkPass<Ev = Fst::Ev, Marker = Fst::Marker, NextPass = Snd>,
    > EventSinkPass for EventSinkPassCombinator<Fst, Snd>
{
    type Ev = Fst::Ev;
    type Marker = Fst::Marker;
    type State = CombinedState<Fst::State, Snd::State>;
    type NextPass = Self;

    fn new_state(&self) -> Self::State {
        match self {
            Self::First(pass) => CombinedState::First(pass.new_state()),
            Self::Next(pass) => CombinedState::Next(pass.new_state()),
        }
    }

    fn event(&self, state: &mut Self::State, event: Self::Ev, range: Range<&Self::Marker>) {
        match self {
            Self::First(pass) => {
                let CombinedState::First(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                pass.event(pass_state, event, range)
            }
            Self::Next(pass) => {
                let CombinedState::Next(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                pass.event(pass_state, event, range)
            }
        }
    }

    fn next_pass(self, state: Self::State, end_marker: &Self::Marker) -> Option<Self::NextPass> {
        match self {
            Self::First(pass) => {
                let CombinedState::First(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                let next_pass = pass.next_pass(pass_state, end_marker)?;
                Some(Self::Next(next_pass))
            }
            Self::Next(pass) => {
                let CombinedState::Next(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                let next_pass = pass.next_pass(pass_state, end_marker)?;
                Some(Self::Next(next_pass))
            }
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum CombinedState<Fst, Snd> {
    First(Fst),
    Next(Snd),
}

pub trait SimpleEventSink: Sized {
    type Ev: Event;
    type State: Clone + PartialEq;

    fn new_state(&self) -> Self::State;
    fn event(&self, state: &mut Self::State, event: Self::Ev);
    fn next_pass(self, state: Self::State) -> Option<Self>;
}

impl<'a, Sink: SimpleEventSink> EventSink<'a> for Sink {
    type Ev = Sink::Ev;
    type Pass<Src: EventSource + 'a> = SimpleEventSinkPass<Sink, Src::Marker>;

    fn start<Src: EventSource + 'a>(
        self,
        _source: EventSourceWithOps<'a, Self::Ev, Src>,
    ) -> Self::Pass<Src> {
        SimpleEventSinkPass {
            sink: self,
            _phantom_marker: PhantomData,
        }
    }
}

pub struct SimpleEventSinkPass<Sink: SimpleEventSink, Marker> {
    sink: Sink,
    _phantom_marker: PhantomData<Marker>,
}

impl<Sink: SimpleEventSink, Marker: Clone + PartialEq> EventSinkPass
    for SimpleEventSinkPass<Sink, Marker>
{
    type Ev = Sink::Ev;
    type Marker = Marker;
    type State = Sink::State;

    fn new_state(&self) -> Self::State {
        self.sink.new_state()
    }

    fn event(&self, state: &mut Self::State, event: Self::Ev, _range: Range<&Self::Marker>) {
        self.sink.event(state, event)
    }

    fn next_pass(
        mut self,
        state: Self::State,
        _end_marker: &Self::Marker,
    ) -> Option<Self::NextPass> {
        self.sink = self.sink.next_pass(state)?;
        Some(self)
    }
}

// We might change this at some point to better support localization.
pub type Message = String;

// Note: EventSource should be thought of as a _reference_ to the source of events. In particular,
// cloning an EventSource creates a new reference to the same actual source, and it does not matter
// which copy diagnostics are reported to.
pub trait EventSource: Clone {
    type Marker: Clone + PartialEq;

    fn diagnostic(&self, range: Range<&Self::Marker>, severity: Severity, msg: Message);

    fn range_event(&self, event: RangeClassEvent, marker: &Self::Marker);

    fn range(&self, class: RangeClass, range: Range<&Self::Marker>) {
        self.range_event(RangeClassEvent::Start(class), range.start);
        self.range_event(RangeClassEvent::End(class), range.end);
    }
}

impl<Src: EventSource> EventSource for Option<Src> {
    type Marker = Src::Marker;

    fn diagnostic(&self, range: Range<&Self::Marker>, severity: Severity, msg: Message) {
        if let Some(source) = self {
            source.diagnostic(range, severity, msg);
        }
    }

    fn range_event(&self, event: RangeClassEvent, marker: &Self::Marker) {
        if let Some(source) = self {
            source.range_event(event, marker);
        }
    }
}

pub struct EventSourceWithOps<'a, Ev: Event, Src: EventSource>(
    pub Src,
    pub Ev::SpecialOps<'a, Src::Marker>,
)
where
    Src::Marker: 'a;

impl<'a, Ev: Event, Src: EventSource> Clone for EventSourceWithOps<'a, Ev, Src>
where
    Src::Marker: 'a,
{
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}

impl<'a, Ev: Event, Src: EventSource> EventSource for EventSourceWithOps<'a, Ev, Src>
where
    Src::Marker: 'a,
{
    type Marker = Src::Marker;

    fn diagnostic(&self, range: Range<&Self::Marker>, severity: Severity, msg: Message) {
        self.0.diagnostic(range, severity, msg)
    }

    fn range_event(&self, event: RangeClassEvent, marker: &Self::Marker) {
        self.0.range_event(event, marker)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Severity {
    Info,
    Warning,
    Error,
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum RangeClassEvent {
    Start(RangeClass),
    End(RangeClass),
}

impl RangeClassEvent {
    pub fn shift_before(&self, other: &Self) -> bool {
        match other {
            RangeClassEvent::Start(other_class) => match self {
                RangeClassEvent::Start(_) => true,
                RangeClassEvent::End(class) => *class != *other_class,
            },
            RangeClassEvent::End(_) => false,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum RangeClass {
    Comment,
    Keyword,
    Number,
    String,
    Paren,
    ParamNotation(ParamScopeClass),
    ParamRef(ParamScopeClass),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum ParamScopeClass {
    Global,
    Local,
    Object,
    Extra,
}

#[derive(Clone, PartialEq, Debug)]
pub enum GroupEvent<Data = ()> {
    Start(Data),
    End,
}

impl<Data> GroupEvent<Data> {
    pub fn apply_to(&self, depth: &mut u32) {
        match self {
            GroupEvent::Start(_) => *depth += 1,
            GroupEvent::End => *depth -= 1,
        }
    }
}

pub mod test_helpers {
    use super::*;

    impl<'a, Ev: Event + Clone + PartialEq> SimpleEventSink for &'a mut Vec<Ev> {
        type Ev = Ev;
        type State = Vec<Ev>;

        fn new_state(&self) -> Self::State {
            Vec::new()
        }

        fn event(&self, state: &mut Self::State, event: Self::Ev) {
            state.push(event)
        }

        fn next_pass(self, state: Self::State) -> Option<Self> {
            *self = state;
            None
        }
    }

    pub trait IntoEvents<T>: Sized {
        fn fill_events(self, result: &mut Vec<T>);

        fn into_events(self) -> Vec<T> {
            let mut result = Vec::new();
            self.fill_events(&mut result);
            result
        }

        fn group<Data>(
            data: Data,
            result: &mut Vec<T>,
            mut map: impl FnMut(GroupEvent<Data>) -> T,
            f: impl FnOnce(&mut Vec<T>),
        ) {
            result.push(map(GroupEvent::Start(data)));
            f(result);
            result.push(map(GroupEvent::End));
        }
    }

    impl<T, Item: IntoEvents<T>> IntoEvents<T> for Option<Item> {
        fn fill_events(self, result: &mut Vec<T>) {
            if let Some(item) = self {
                item.fill_events(result);
            }
        }
    }

    impl<T, Item: IntoEvents<T>> IntoEvents<T> for Vec<Item> {
        fn fill_events(self, result: &mut Vec<T>) {
            for group in self {
                group.fill_events(result);
            }
        }
    }

    pub trait IntoRangeClassEvents: Sized {
        fn fill_events(self, result: &mut Vec<(RangeClassEvent, usize)>, cur_len: &mut usize);

        fn into_events(self) -> (Vec<(RangeClassEvent, usize)>, usize) {
            let mut result = Vec::new();
            let mut len = 0;
            self.fill_events(&mut result, &mut len);
            (result, len)
        }
    }

    pub type RangeClassTree<'a> = Vec<RangeClassTreeNode<'a>>;

    impl IntoRangeClassEvents for RangeClassTree<'_> {
        fn fill_events(self, result: &mut Vec<(RangeClassEvent, usize)>, cur_len: &mut usize) {
            for item in self {
                item.fill_events(result, cur_len);
            }
        }
    }

    pub enum RangeClassTreeNode<'a> {
        Text(&'a str),
        Range(RangeClass, RangeClassTree<'a>),
    }

    impl IntoRangeClassEvents for RangeClassTreeNode<'_> {
        fn fill_events(self, result: &mut Vec<(RangeClassEvent, usize)>, cur_len: &mut usize) {
            match self {
                RangeClassTreeNode::Text(s) => *cur_len += s.len(),
                RangeClassTreeNode::Range(class, items) => {
                    result.push((RangeClassEvent::Start(class), *cur_len));
                    items.fill_events(result, cur_len);
                    result.push((RangeClassEvent::End(class), *cur_len));
                }
            }
        }
    }
}

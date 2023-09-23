//! An "event translator" is an event sink that produces other events depending on the incoming
//! events and its internal state. Given a sink for the outgoing events, the sink state of the
//! translator is the combination of the translator state and the target sink state.
//!
//! An example is a tokenizer that receives characters and outputs tokens.
//!
//! Event translators make their split state visible, to enable reuse of unchanged parts when input
//! events are only changed within a small region. Instead of replaying input events in this case,
//! we can replay output events once we detect that the translator state (excluding the target sink
//! state) is unchanged compared to its original state when the replayed input events had originally
//! been sent.
//! If the target sink is again an event translator, the same mechanism can be applied recursively,
//! so that ideally only the most high-level events need to be replayed fully.

use std::{marker::PhantomData, ops::Range};

use crate::{event::*, event_source::*};

pub trait EventTranslator<'a> {
    type In: Event;
    type Out: Event;

    type Pass<Src: EventSource + 'a>: EventTranslatorPass<
            In = Self::In,
            Out = Self::Out,
            Marker = Src::Marker,
            NextPass = Self::Pass<Src>,
        > + SpecialOpsGetter<<Self::Out as Event>::SpecialOps<'a, Src::Marker>>
        + 'a;

    // The number of outer passes is determined by the sink of the outgoing events, which requires
    // events to be repeated a certain number of times.
    fn start<Src: EventSource + 'a>(
        &self,
        source: EventSourceWithOps<'a, Self::In, Src>,
    ) -> Self::Pass<Src>;
}

pub struct TranslatorInst<'a, T: EventTranslator<'a>, Sink: EventSink<'a, Ev = T::Out>> {
    _phantom_a: PhantomData<&'a ()>,
    pub translator: T,
    pub sink: Sink,
}

impl<'a, T: EventTranslator<'a>, Sink: EventSink<'a, Ev = T::Out>> TranslatorInst<'a, T, Sink> {
    pub fn new(translator: T, sink: Sink) -> Self {
        TranslatorInst {
            _phantom_a: PhantomData,
            translator,
            sink,
        }
    }
}

impl<'a, T: EventTranslator<'a>, Sink: EventSink<'a, Ev = T::Out>> EventSink<'a>
    for TranslatorInst<'a, T, Sink>
{
    type Ev = T::In;

    type Pass<Src: EventSource + 'a> = TranslatorPassInst<'a, T, Src, Sink::Pass<Src>>;

    fn start<Src: EventSource + 'a>(
        self,
        source: EventSourceWithOps<'a, Self::Ev, Src>,
    ) -> Self::Pass<Src> {
        let translator_pass = self
            .translator
            .start(EventSourceWithOps(Some(source.0.clone()), source.1.clone()));
        let sink_pass = self
            .sink
            .start(EventSourceWithOps(source.0, translator_pass.special_ops()));
        TranslatorPassInst {
            translator: self.translator,
            special_ops: source.1,
            translator_pass,
            sink_pass,
        }
    }
}

pub trait EventTranslatorPass: Sized {
    type In: Event;
    type Out: Event;
    type Marker: Clone + PartialEq;

    // The translator can optionally specify multiple inner passes, optionally with different types.
    type NextPass: EventTranslatorPass<In = Self::In, Out = Self::Out, Marker = Self::Marker> =
        Self;

    type State: Clone + PartialEq;

    fn new_state(&self) -> Self::State;

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    );

    fn next_pass(
        self,
        state: Self::State,
        end_marker: &Self::Marker,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass>;
}

// Helper to combine two types that implement `EventTranslatorPass` into one. Can be used
// recursively in `Snd`.
pub enum EventTranslatorPassCombinator<
    Fst: EventTranslatorPass<NextPass = Snd>,
    Snd: EventTranslatorPass<In = Fst::In, Out = Fst::Out, Marker = Fst::Marker, NextPass = Snd>,
> {
    First(Fst),
    Next(Snd),
}

impl<
        Fst: EventTranslatorPass<NextPass = Snd>,
        Snd: EventTranslatorPass<In = Fst::In, Out = Fst::Out, Marker = Fst::Marker, NextPass = Snd>,
    > EventTranslatorPass for EventTranslatorPassCombinator<Fst, Snd>
{
    type In = Fst::In;
    type Out = Fst::Out;
    type Marker = Fst::Marker;
    type NextPass = Self;
    type State = CombinedState<Fst::State, Snd::State>;

    fn new_state(&self) -> Self::State {
        match self {
            Self::First(pass) => CombinedState::First(pass.new_state()),
            Self::Next(pass) => CombinedState::Next(pass.new_state()),
        }
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) {
        match self {
            Self::First(pass) => {
                let CombinedState::First(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                pass.event(pass_state, event, range, out)
            }
            Self::Next(pass) => {
                let CombinedState::Next(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                pass.event(pass_state, event, range, out)
            }
        }
    }

    fn next_pass(
        self,
        state: Self::State,
        end_marker: &Self::Marker,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        match self {
            Self::First(pass) => {
                let CombinedState::First(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                let next_pass = pass.next_pass(pass_state, end_marker, out)?;
                Some(Self::Next(next_pass))
            }
            Self::Next(pass) => {
                let CombinedState::Next(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                let next_pass = pass.next_pass(pass_state, end_marker, out)?;
                Some(Self::Next(next_pass))
            }
        }
    }
}

pub struct TranslatorPassInst<
    'a,
    T: EventTranslator<'a>,
    Src: EventSource + 'a,
    SP: EventSinkPass<Ev = T::Out, Marker = Src::Marker, NextPass = SP>,
> {
    pub translator: T,
    pub special_ops: <T::In as Event>::SpecialOps<'a, Src::Marker>,
    pub translator_pass: T::Pass<Option<Src>>,
    pub sink_pass: SP,
}

impl<
        'a,
        T: EventTranslator<'a>,
        Src: EventSource + 'a,
        SP: EventSinkPass<Ev = T::Out, Marker = Src::Marker, NextPass = SP>,
    > EventSinkPass for TranslatorPassInst<'a, T, Src, SP>
{
    type Ev = T::In;
    type Marker = Src::Marker;
    type State = TranslatorStateInst<T::Pass<Option<Src>>, SP>;
    type NextPass = Self;

    fn new_state(&self) -> Self::State {
        TranslatorStateInst {
            translator_state: self.translator_pass.new_state(),
            sink_state: self.sink_pass.new_state(),
        }
    }

    fn event(&self, state: &mut Self::State, event: T::In, range: Range<&Src::Marker>) {
        self.translator_pass.event(
            &mut state.translator_state,
            event,
            range,
            |out, out_range| {
                EventSinkPass::event(&self.sink_pass, &mut state.sink_state, out, out_range)
            },
        )
    }

    fn next_pass(
        mut self,
        mut state: Self::State,
        end_marker: &Src::Marker,
    ) -> Option<Self::NextPass> {
        if let Some(next_translator_pass) =
            self.translator_pass
                .next_pass(state.translator_state, end_marker, |out, out_range| {
                    EventSinkPass::event(&self.sink_pass, &mut state.sink_state, out, out_range)
                })
        {
            self.translator_pass = next_translator_pass;
        } else {
            self.sink_pass = self.sink_pass.next_pass(state.sink_state, end_marker)?;
            self.translator_pass = self
                .translator
                .start(EventSourceWithOps(None, self.special_ops.clone()));
        }
        Some(self)
    }
}

pub struct TranslatorStateInst<
    TP: EventTranslatorPass,
    SP: EventSinkPass<Ev = TP::Out, Marker = TP::Marker>,
> {
    pub translator_state: TP::State,
    pub sink_state: SP::State,
}

// Unfortunately, #[derive] fails to work in these generic cases.
impl<TP: EventTranslatorPass, SP: EventSinkPass<Ev = TP::Out, Marker = TP::Marker>> Clone
    for TranslatorStateInst<TP, SP>
{
    fn clone(&self) -> Self {
        Self {
            translator_state: self.translator_state.clone(),
            sink_state: self.sink_state.clone(),
        }
    }
}

impl<TP: EventTranslatorPass, SP: EventSinkPass<Ev = TP::Out, Marker = TP::Marker>> PartialEq
    for TranslatorStateInst<TP, SP>
{
    fn eq(&self, other: &Self) -> bool {
        self.translator_state == other.translator_state && self.sink_state == other.sink_state
    }
}

pub trait SpecialOpsGetter<SpecialOps> {
    fn special_ops(&self) -> SpecialOps;
}

impl<T> SpecialOpsGetter<()> for T {
    fn special_ops(&self) -> () {
        ()
    }
}

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

use crate::event::*;

pub trait EventTranslator<'a> {
    type In: Event;
    type Out: Event;

    type OuterPass<Src: EventSource + 'a>: EventTranslatorOuterPass<In = Self::In, Out = Self::Out, Marker = Src::Marker>
        + 'a;

    fn start<Src: EventSource + 'a>(
        self,
        source: &'a Src,
        special_ops: <Self::In as Event>::SpecialOps<'a, Src::Marker>,
    ) -> (
        Self::OuterPass<Src>,
        <Self::Out as Event>::SpecialOps<'a, Src::Marker>,
    );
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

    type Pass<Src: EventSource + 'a> = TranslatorInnerPassInst<T::OuterPass<Src>, Sink::Pass<Src>>;

    fn start<Src: EventSource + 'a>(
        self,
        source: &'a Src,
        special_ops: <Self::Ev as Event>::SpecialOps<'a, Src::Marker>,
    ) -> Self::Pass<Src> {
        let (translator_pass, out_special_ops) = self.translator.start(source, special_ops);
        let sink_pass = self.sink.start(source, out_special_ops);
        let mut outer_pass = TranslatorOuterPassInst {
            translator_pass,
            sink_pass,
        };
        let inner_pass = outer_pass.translator_pass.start_inner();
        TranslatorInnerPassInst {
            outer_pass,
            inner_pass,
        }
    }
}

// The number of outer passes is determined by the sink of the outgoing events, which requires
// events to be repeated a certain number of times.
pub trait EventTranslatorOuterPass {
    type In: Event;
    type Out: Event;
    type Marker: Clone + PartialEq;

    type InnerPass: EventTranslatorInnerPass<
        In = Self::In,
        Out = Self::Out,
        Marker = Self::Marker,
        NextInnerPass = Self::InnerPass,
    >;

    fn start_inner(&mut self) -> Self::InnerPass;
}

pub struct TranslatorOuterPassInst<
    TOP: EventTranslatorOuterPass,
    SP: EventSinkPass<Ev = TOP::Out, Marker = TOP::Marker>,
> {
    pub translator_pass: TOP,
    pub sink_pass: SP,
}

// The translator can optionally specify multiple inner passes, optionally with different types.
pub trait EventTranslatorInnerPass: Sized {
    type In: Event;
    type Out: Event;
    type Marker: Clone + PartialEq;

    type NextInnerPass: EventTranslatorInnerPass<
        In = Self::In,
        Out = Self::Out,
        Marker = Self::Marker,
    > = Self;

    type State: Clone + PartialEq;

    fn new_state(&self) -> Self::State;

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    );

    fn next_inner_pass(
        self,
        state: Self::State,
        end_marker: &Self::Marker,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextInnerPass>;
}

// Helper to combine two types that implement `EventTranslatorInnerPass` into one. Can be used
// recursively in `Snd`.
pub enum EventTranslatorInnerPassCombinator<
    Fst: EventTranslatorInnerPass<NextInnerPass = Snd>,
    Snd: EventTranslatorInnerPass<
        In = Fst::In,
        Out = Fst::Out,
        Marker = Fst::Marker,
        NextInnerPass = Snd,
    >,
> {
    First(Fst),
    Next(Snd),
}

impl<
        Fst: EventTranslatorInnerPass<NextInnerPass = Snd>,
        Snd: EventTranslatorInnerPass<
            In = Fst::In,
            Out = Fst::Out,
            Marker = Fst::Marker,
            NextInnerPass = Snd,
        >,
    > EventTranslatorInnerPass for EventTranslatorInnerPassCombinator<Fst, Snd>
{
    type In = Fst::In;
    type Out = Fst::Out;
    type Marker = Fst::Marker;
    type NextInnerPass = Self;
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

    fn next_inner_pass(
        self,
        state: Self::State,
        end_marker: &Self::Marker,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextInnerPass> {
        match self {
            Self::First(pass) => {
                let CombinedState::First(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                let next_pass = pass.next_inner_pass(pass_state, end_marker, out)?;
                Some(Self::Next(next_pass))
            }
            Self::Next(pass) => {
                let CombinedState::Next(pass_state) = state else {
                    panic!("inconsistent pass combinator state");
                };
                let next_pass = pass.next_inner_pass(pass_state, end_marker, out)?;
                Some(Self::Next(next_pass))
            }
        }
    }
}

pub struct TranslatorInnerPassInst<
    TOP: EventTranslatorOuterPass,
    SP: EventSinkPass<Ev = TOP::Out, Marker = TOP::Marker, NextPass = SP>,
> {
    pub outer_pass: TranslatorOuterPassInst<TOP, SP>,
    pub inner_pass: TOP::InnerPass,
}

impl<
        TOP: EventTranslatorOuterPass,
        SP: EventSinkPass<Ev = TOP::Out, Marker = TOP::Marker, NextPass = SP>,
    > EventSinkPass for TranslatorInnerPassInst<TOP, SP>
{
    type Ev = TOP::In;
    type Marker = TOP::Marker;
    type State = TranslatorStateInst<TOP::InnerPass, SP>;
    type NextPass = Self;

    fn new_state(&self) -> Self::State {
        TranslatorStateInst {
            translator_state: self.inner_pass.new_state(),
            sink_state: self.outer_pass.sink_pass.new_state(),
        }
    }

    fn event(&self, state: &mut Self::State, event: TOP::In, range: Range<&TOP::Marker>) {
        self.inner_pass.event(
            &mut state.translator_state,
            event,
            range,
            |out, out_range| {
                EventSinkPass::event(
                    &self.outer_pass.sink_pass,
                    &mut state.sink_state,
                    out,
                    out_range,
                )
            },
        )
    }

    fn next_pass(
        mut self,
        mut state: Self::State,
        end_marker: &TOP::Marker,
    ) -> Option<Self::NextPass> {
        if let Some(next_inner_pass) =
            self.inner_pass
                .next_inner_pass(state.translator_state, end_marker, |out, out_range| {
                    EventSinkPass::event(
                        &self.outer_pass.sink_pass,
                        &mut state.sink_state,
                        out,
                        out_range,
                    )
                })
        {
            self.inner_pass = next_inner_pass;
        } else {
            self.outer_pass.sink_pass = self
                .outer_pass
                .sink_pass
                .next_pass(state.sink_state, end_marker)?;
            self.inner_pass = self.outer_pass.translator_pass.start_inner();
        }
        Some(self)
    }
}

pub struct TranslatorStateInst<
    TIP: EventTranslatorInnerPass,
    SP: EventSinkPass<Ev = TIP::Out, Marker = TIP::Marker>,
> {
    pub translator_state: TIP::State,
    pub sink_state: SP::State,
}

// Unfortunately, #[derive] fails to work in these generic cases.
impl<TIP: EventTranslatorInnerPass, SP: EventSinkPass<Ev = TIP::Out, Marker = TIP::Marker>> Clone
    for TranslatorStateInst<TIP, SP>
{
    fn clone(&self) -> Self {
        Self {
            translator_state: self.translator_state.clone(),
            sink_state: self.sink_state.clone(),
        }
    }
}

impl<TIP: EventTranslatorInnerPass, SP: EventSinkPass<Ev = TIP::Out, Marker = TIP::Marker>>
    PartialEq for TranslatorStateInst<TIP, SP>
{
    fn eq(&self, other: &Self) -> bool {
        self.translator_state == other.translator_state && self.sink_state == other.sink_state
    }
}

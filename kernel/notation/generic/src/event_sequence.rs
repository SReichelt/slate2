use std::ops::Range;

use crate::{event::*, event_source::*};

pub trait EventSequence<'a> {
    type Ev: Event;
    type Marker: Clone + PartialEq;

    fn for_each(&self, f: impl FnMut(Self::Ev, Range<&Self::Marker>)) -> Self::Marker;

    fn special_ops(&'a self) -> <Self::Ev as Event>::SpecialOps<'a, Self::Marker>;

    fn run<Src: EventSource<Marker = Self::Marker> + 'a, Sink: EventSink<'a, Ev = Self::Ev>>(
        &'a self,
        source: Src,
        sink: Sink,
    ) {
        let pass = sink.start(EventSourceWithOps(source, self.special_ops()));
        self.run_pass(pass)
    }

    fn run_pass<Pass: EventSinkPass<Ev = Self::Ev, Marker = Self::Marker>>(&self, pass: Pass) {
        let mut state = pass.new_state();
        let end_marker = self.for_each(|event, range| pass.event(&mut state, event, range));
        if let Some(next_pass) = pass.next_pass(state, &end_marker) {
            self.run_pass(next_pass)
        }
    }

    fn start_marker() -> Self::Marker;
}

impl<'a, T: EventSequence<'a>, Extra> EventSequence<'a> for (T, Extra) {
    type Ev = T::Ev;
    type Marker = T::Marker;

    fn for_each(&self, f: impl FnMut(Self::Ev, Range<&Self::Marker>)) -> Self::Marker {
        self.0.for_each(f)
    }

    fn special_ops(&'a self) -> <Self::Ev as Event>::SpecialOps<'a, Self::Marker> {
        self.0.special_ops()
    }

    fn start_marker() -> Self::Marker {
        T::start_marker()
    }
}

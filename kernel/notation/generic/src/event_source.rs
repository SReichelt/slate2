use std::ops::Range;

use crate::event::*;

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

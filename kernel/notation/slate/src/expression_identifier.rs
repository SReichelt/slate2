use std::ops::Range;

use slate_kernel_notation_generic::{event::*, event_translator::*};

use crate::parameter_identifier::*;

#[derive(Clone, PartialEq, Debug)]
pub enum ExpressionEvent<'a> {
    Token(ParameterEvent<'a>),
}

impl Event for ExpressionEvent<'_> {}

pub struct ExpressionIdentifier;

impl<'a> EventTranslator<'a> for ExpressionIdentifier {
    type In = ParameterEvent<'a>;
    type Out = ExpressionEvent<'a>;
    type Pass<Src: EventSource + 'a> = EventTranslatorPassCombinator<
        GlobalParamRecordingPass<'a, Src>,
        ExpressionOutputPass<'a, Src>,
    >;

    fn start<Src: EventSource + 'a>(
        &self,
        source: EventSourceWithOps<'a, Self::In, Src>,
    ) -> Self::Pass<Src> {
        EventTranslatorPassCombinator::First(GlobalParamRecordingPass { source })
    }
}

pub struct GlobalParamRecordingPass<'a, Src: EventSource + 'a> {
    source: EventSourceWithOps<'a, ParameterEvent<'a>, Src>,
}

impl<'a, Src: EventSource + 'a> EventTranslatorPass for GlobalParamRecordingPass<'a, Src> {
    type In = ParameterEvent<'a>;
    type Out = ExpressionEvent<'a>;
    type Marker = Src::Marker;
    type State = NotationsRecordingState<'a>;
    type NextPass = ExpressionOutputPass<'a, Src>;

    fn new_state(&self) -> Self::State {
        NotationsRecordingState {
            recorded_notations: Vec::new(),
            current_group_state: None,
        }
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        _range: Range<&Self::Marker>,
        _out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) {
        self.notations_event(state, event);
    }

    fn next_pass(
        self,
        state: Self::State,
        _end_marker: &Self::Marker,
        _out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        Some(ExpressionOutputPass {
            source: self.source,
            global_notations: state.recorded_notations,
        })
    }
}

impl<'a, Src: EventSource + 'a> GlobalParamRecordingPass<'a, Src> {
    fn notations_event(
        &self,
        state: &mut NotationsRecordingState<'a>,
        event: ParameterEvent<'a>,
    ) -> Option<ParameterEvent<'a>> {
        if let Some(group_state) = &mut state.current_group_state {
            if let Some(event) = self.group_event(group_state, &mut state.recorded_notations, event)
            {
                if let ParameterEvent::SectionItem(GroupEvent::End) = event {
                    state.current_group_state = None;
                }
            }
            None
        } else if let ParameterEvent::SectionItem(GroupEvent::Start(_)) = event {
            state.current_group_state = Some(Box::new(GroupNotationRecordingState {
                parameterization_state: NotationsRecordingState {
                    recorded_notations: Vec::new(),
                    current_group_state: None,
                },
            }));
            None
        } else {
            Some(event)
        }
    }

    fn group_event(
        &self,
        state: &mut GroupNotationRecordingState<'a>,
        recorded_notations: &mut Vec<NotationExpression<'a>>,
        event: ParameterEvent<'a>,
    ) -> Option<ParameterEvent<'a>> {
        if let Some(event) = self.notations_event(&mut state.parameterization_state, event) {
            Some(event)
        } else {
            None
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct NotationsRecordingState<'a> {
    recorded_notations: Vec<NotationExpression<'a>>,
    current_group_state: Option<Box<GroupNotationRecordingState<'a>>>,
}

#[derive(Clone, PartialEq)]
struct GroupNotationRecordingState<'a> {
    parameterization_state: NotationsRecordingState<'a>,
    // TODO
}

pub struct ExpressionOutputPass<'a, Src: EventSource + 'a> {
    source: EventSourceWithOps<'a, ParameterEvent<'a>, Src>,
    global_notations: Vec<NotationExpression<'a>>,
}

impl<'a, Src: EventSource + 'a> EventTranslatorPass for ExpressionOutputPass<'a, Src> {
    type In = ParameterEvent<'a>;
    type Out = ExpressionEvent<'a>;
    type Marker = Src::Marker;
    type State = ExpressionOutputState;

    fn new_state(&self) -> Self::State {
        ExpressionOutputState
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) {
    }

    fn next_pass(
        self,
        state: Self::State,
        end_marker: &Self::Marker,
        out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        None
    }
}

#[derive(Clone, PartialEq)]
pub struct ExpressionOutputState;

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use anyhow::Result;

    use slate_kernel_notation_generic::{
        char_slice::{test_helpers::*, *},
        event::test_helpers::*,
    };

    use crate::{metamodel::test_helpers::*, parenthesis_matcher::*, tokenizer::*};

    use super::*;

    #[test]
    fn token_diagnostics() -> Result<(), Message> {
        // Verify that diagnostics from earlier passes are only reported once, even though those
        // passes are executed multiple times.
        test_expression_identification(
            "%slate \"test\"; x,,y : (\"endless",
            Document {
                _phantom_a: PhantomData,
            },
            &[
                TestDiagnosticMessage {
                    range_text: "\"endless".into(),
                    severity: Severity::Error,
                    msg: "unterminated string".into(),
                },
                TestDiagnosticMessage {
                    range_text: "(\"endless".into(),
                    severity: Severity::Error,
                    msg: "unmatched parenthesis: ')' expected".into(),
                },
                TestDiagnosticMessage {
                    range_text: "".into(),
                    severity: Severity::Error,
                    msg: "parameter expected".into(),
                },
            ],
        )?;
        Ok(())
    }

    struct Document<'a> {
        _phantom_a: PhantomData<&'a ()>,
    }

    impl<'a> IntoEvents<ExpressionEvent<'a>> for Document<'a> {
        fn fill_events(self, result: &mut Vec<ExpressionEvent<'a>>) {}
    }

    fn test_expression_identification(
        input: &str,
        expected_document: Document,
        expected_diagnostics: &[TestDiagnosticMessage],
    ) -> Result<(), Message> {
        let metamodel = TestMetaModel;
        let mut expression_events = Vec::new();
        let expression_sink = TranslatorInst::new(ExpressionIdentifier, &mut expression_events);
        let param_sink = TranslatorInst::new(ParameterIdentifier::new(&metamodel), expression_sink);
        let token_sink = TranslatorInst::new(ParenthesisMatcher, param_sink);
        let char_sink = TranslatorInst::new(Tokenizer, token_sink);
        let diag_sink = DiagnosticsRecorder::new(input);
        let source = CharSliceEventSource::new(input, &diag_sink)?;
        source.run(char_sink);
        assert_eq!(expression_events, expected_document.into_events());
        assert_eq!(diag_sink.diagnostics(), expected_diagnostics);
        Ok(())
    }
}

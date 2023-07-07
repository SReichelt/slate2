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
    type State = GlobalParamRecordingState;
    type NextPass = ExpressionOutputPass<'a, Src>;

    fn new_state(&self) -> Self::State {
        GlobalParamRecordingState { params: Vec::new() }
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: std::ops::Range<&Self::Marker>,
        out: impl FnMut(Self::Out, std::ops::Range<&Self::Marker>),
    ) {
    }

    fn next_pass(
        self,
        state: Self::State,
        end_marker: &Self::Marker,
        out: impl FnMut(Self::Out, std::ops::Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        Some(ExpressionOutputPass {
            source: self.source,
            global_param_state: state,
        })
    }
}

#[derive(Clone, PartialEq)]
pub struct GlobalParamRecordingState {
    params: Vec<RecordedParam>,
}

#[derive(Clone, PartialEq)]
struct RecordedParam {
    notation: Vec<NotationToken>,
}

#[derive(Clone, PartialEq)]
enum NotationToken {}

pub struct ExpressionOutputPass<'a, Src: EventSource + 'a> {
    source: EventSourceWithOps<'a, ParameterEvent<'a>, Src>,
    global_param_state: GlobalParamRecordingState,
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
        range: std::ops::Range<&Self::Marker>,
        out: impl FnMut(Self::Out, std::ops::Range<&Self::Marker>),
    ) {
    }

    fn next_pass(
        self,
        state: Self::State,
        end_marker: &Self::Marker,
        out: impl FnMut(Self::Out, std::ops::Range<&Self::Marker>),
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
                    range_text: "".into(),
                    severity: Severity::Error,
                    msg: "parameter expected".into(),
                },
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
                    msg: "';' expected".into(),
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
        let mut expression_events = Vec::new();
        let expression_sink = TranslatorInst::new(ExpressionIdentifier, &mut expression_events);
        let param_sink = TranslatorInst::new(
            ParameterIdentifier::new(TestMetaModelGetter),
            expression_sink,
        );
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

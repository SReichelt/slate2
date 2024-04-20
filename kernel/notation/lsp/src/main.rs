use std::collections::HashMap;

use tokio::sync::{Mutex, OnceCell};
use tower_lsp::jsonrpc::{Error, ErrorCode, Result};
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

mod document;
use document::*;

struct SlateServer {
    client: Client,
    settings: OnceCell<ServerSettings>,
    state: Mutex<ServerState>,
}

impl SlateServer {
    fn new(client: Client) -> Self {
        SlateServer {
            client,
            settings: OnceCell::new(),
            state: Mutex::new(ServerState::new()),
        }
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for SlateServer {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        let mut settings = ServerSettings {
            position_encoding: PositionEncoding::UTF16,
        };

        let mut position_encoding = None;
        if let Some(capabilities) = params.capabilities.general {
            if let Some(position_encodings) = capabilities.position_encodings {
                if position_encodings.contains(&PositionEncodingKind::UTF8) {
                    position_encoding = Some(PositionEncodingKind::UTF8);
                    settings.position_encoding = PositionEncoding::UTF8;
                } else if position_encodings.contains(&PositionEncodingKind::UTF32) {
                    position_encoding = Some(PositionEncodingKind::UTF32);
                    settings.position_encoding = PositionEncoding::UTF32;
                } else if position_encodings.contains(&PositionEncodingKind::UTF16) {
                    position_encoding = Some(PositionEncodingKind::UTF16);
                    settings.position_encoding = PositionEncoding::UTF16;
                }
            }
        }

        self.client
            .log_message(
                MessageType::INFO,
                format!("initializing with settings: {settings:?}"),
            )
            .await;

        let Ok(()) = self.settings.set(settings) else {
            return Err(Error::invalid_request());
        };

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                position_encoding,
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::INCREMENTAL),
                        save: Some(TextDocumentSyncSaveOptions::Supported(true)),
                        ..Default::default()
                    },
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            legend: SemanticTokensLegend {
                                token_types: vec![SemanticTokenType::COMMENT],
                                token_modifiers: Vec::new(),
                            },
                            full: Some(SemanticTokensFullOptions::Delta { delta: Some(true) }),
                            ..Default::default()
                        },
                    ),
                ),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let settings = self.settings.get().unwrap();
        let document = Document::new(settings.position_encoding, &params.text_document.text);
        let mut state = self.state.lock().await;
        state
            .open_documents
            .insert(params.text_document.uri, document);
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, format!("did_change"))
            .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {}

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let mut state = self.state.lock().await;
        state.open_documents.remove(&params.text_document.uri);
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let mut state = self.state.lock().await;
        let Some(document) = state.open_documents.get_mut(&params.text_document.uri) else {
            return Err(Error::invalid_params("document not open"));
        };

        Ok(None)
    }

    async fn semantic_tokens_full_delta(
        &self,
        params: SemanticTokensDeltaParams,
    ) -> Result<Option<SemanticTokensFullDeltaResult>> {
        // TODO
        Ok(None)
    }
}

#[derive(Debug)]
struct ServerSettings {
    position_encoding: PositionEncoding,
}

struct ServerState {
    open_documents: HashMap<Url, Document>,
}

impl ServerState {
    fn new() -> Self {
        ServerState {
            open_documents: HashMap::new(),
        }
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(SlateServer::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}

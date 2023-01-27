use anyhow::{Context, Error, Result};

pub trait ErrorPrefix {
    fn with_prefix(self, f: impl FnOnce() -> String) -> Self;
}

impl<T> ErrorPrefix for Result<T> {
    fn with_prefix(self, f: impl FnOnce() -> String) -> Self {
        self.with_context(f)
    }
}

pub trait CombineErrors {
    fn combine(&self) -> Error;
}

impl CombineErrors for Vec<Error> {
    fn combine(&self) -> Error {
        Error::msg(
            self.iter()
                .map(|err| {
                    err.chain()
                        .map(|cause| cause.to_string())
                        .collect::<Vec<String>>()
                        .join(": ")
                })
                .collect::<Vec<String>>()
                .join("\n\n"),
        )
    }
}

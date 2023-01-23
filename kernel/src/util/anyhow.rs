use anyhow::{Context, Result};

pub trait ErrorPrefix {
    fn with_prefix(self, f: impl FnOnce() -> String) -> Self;
}

impl<T> ErrorPrefix for Result<T> {
    fn with_prefix(self, f: impl FnOnce() -> String) -> Self {
        self.with_context(f)
    }
}

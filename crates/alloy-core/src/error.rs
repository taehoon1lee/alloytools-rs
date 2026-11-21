//! Port of edu.mit.csail.sdg.alloy4.{Pos, Err, ErrorSyntax, ErrorType, ErrorFatal, ErrorWarning}.

use std::fmt;

/// Source position. `line`/`col` are 1-based like Java's `Pos.y` / `Pos.x`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pos {
    pub file: String,
    pub line: i32,
    pub col: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    /// Java `ErrorSyntax` -> harness status `syntax_error`
    Syntax,
    /// Java `ErrorType` -> harness status `type_error`
    Type,
    /// Java `ErrorFatal`/`ErrorAPI`/other -> harness status `error`
    Other,
    /// Feature not ported yet -> harness status `unsupported` (always counted as a failure)
    Unsupported,
}

#[derive(Debug, Clone)]
pub struct AlloyError {
    pub kind: ErrorKind,
    pub pos: Option<Pos>,
    pub msg: String,
}

impl AlloyError {
    pub fn new(kind: ErrorKind, pos: Option<Pos>, msg: impl Into<String>) -> Self {
        AlloyError { kind, pos, msg: msg.into() }
    }
    pub fn syntax(pos: Pos, msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Syntax, Some(pos), msg)
    }
    pub fn type_err(pos: Pos, msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Type, Some(pos), msg)
    }
    pub fn unsupported(msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Unsupported, None, msg)
    }
    /// Harness status string for a file-level failure.
    pub fn status_str(&self) -> &'static str {
        match self.kind {
            ErrorKind::Syntax => "syntax_error",
            ErrorKind::Type => "type_error",
            ErrorKind::Other => "error",
            ErrorKind::Unsupported => "unsupported",
        }
    }
}

impl fmt::Display for AlloyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.pos {
            Some(p) => write!(f, "{:?} at {}:{}:{}: {}", self.kind, p.file, p.line, p.col, self.msg),
            None => write!(f, "{:?}: {}", self.kind, self.msg),
        }
    }
}

impl std::error::Error for AlloyError {}

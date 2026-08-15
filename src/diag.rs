//! Diagnostics: errors, warnings, hints and notes with source spans.

use std::fmt::Write;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

impl Severity {
    pub fn label(&self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
        }
    }
}

/// A source span: 1-based line, 1-based column, length.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub line: usize,
    pub col: usize,
    pub len: usize,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub span: Span,
    pub message: String,
    /// Stable machine-readable kind (e.g. `goal-not-proven`,
    /// `premise-not-established`, `wrong-result`) used by the `-e:` bypass.
    pub kind: &'static str,
    /// Optional `hint:` line.
    pub hint: Option<String>,
    /// Optional `note:` line.
    pub note: Option<String>,
}

impl Diagnostic {
    pub fn error(span: Span, msg: impl Into<String>) -> Diagnostic {
        Diagnostic {
            severity: Severity::Error,
            span,
            message: msg.into(),
            kind: "",
            hint: None,
            note: None,
        }
    }

    pub fn warning(span: Span, msg: impl Into<String>) -> Diagnostic {
        Diagnostic {
            severity: Severity::Warning,
            span,
            message: msg.into(),
            kind: "",
            hint: None,
            note: None,
        }
    }

    pub fn with_kind(mut self, kind: &'static str) -> Diagnostic {
        self.kind = kind;
        self
    }

    pub fn with_hint(mut self, hint: impl Into<String>) -> Diagnostic {
        self.hint = Some(hint.into());
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Diagnostic {
        self.note = Some(note.into());
        self
    }

    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }
}

/// Normalize a bypass name for comparison: strip separators and lower-case,
/// so `GoalNotProven`, `goal-not-proven` and `goalnotproven` all match the
/// diagnostic kind `goal-not-proven`.
fn normalize_name(n: &str) -> String {
    n.chars().filter(|c| c.is_alphanumeric()).flat_map(|c| c.to_lowercase()).collect()
}

/// Downgrade diagnostics whose kind is listed in `names` (the `-e:` bypass)
/// from errors to warnings, attaching a note that the issue was assumed.
pub fn bypass_errors(diags: Vec<Diagnostic>, names: &[String]) -> Vec<Diagnostic> {
    let normalized: Vec<String> = names.iter().map(|n| normalize_name(n)).collect();
    let mut out = Vec::with_capacity(diags.len());
    for mut d in diags {
        let dk = normalize_name(d.kind);
        if d.is_error() && normalized.iter().any(|n| *n == dk) {
            let original = normalize_name(&d.kind);
            let display = names
                .iter()
                .find(|n| normalize_name(n) == original)
                .cloned()
                .unwrap_or_else(|| d.kind.to_string());
            d.severity = Severity::Warning;
            d.note = Some(format!("assumed (bypassed with -e:{})", display));
        }
        out.push(d);
    }
    out
}

/// Render a diagnostic in the style shown by the language spec:
///
/// ```text
/// example.geo:42: error: Wrong result: IsMedian(D,BC) -> BD=BC
///  42 | (IsIsosceles(ABC)=true && IsPrependicular(AD,BC)) -> IsMedian(D,BC)=True -> BD=BC
///     |                                                                             ^^^^^
/// hint: modify BD=BC to BD=DC
/// ```
pub fn render_diag(source: &str, lines: &[String], diag: &Diagnostic) -> String {
    let mut out = String::new();
    let s = diag.span;
    writeln!(
        out,
        "{}:{}:{}: {}: {}",
        source,
        s.line,
        s.col,
        diag.severity.label(),
        diag.message
    )
    .unwrap();

    if s.line > 0 && s.line <= lines.len() {
        let src_line = &lines[s.line - 1];
        let line_num = s.line.to_string();
        let pad = " ".repeat(line_num.len());
        writeln!(out, " {} | {}", line_num, src_line).unwrap();
        let mut caret = String::new();
        let start = s.col.saturating_sub(1);
        let caret_len = s.len.max(1);
        for _ in 0..start {
            caret.push(' ');
        }
        for _ in 0..caret_len {
            caret.push('^');
        }
        writeln!(out, " {} | {}", pad, caret).unwrap();
    }

    if let Some(h) = &diag.hint {
        writeln!(out, "hint: {}", h).unwrap();
    }
    if let Some(n) = &diag.note {
        writeln!(out, "note: {}", n).unwrap();
    }

    out.trim_end().to_string()
}
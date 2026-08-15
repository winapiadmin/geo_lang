//! Tokenizer for the .geo language.
//!
//! Handles `//` line comments, `/* ... */` block comments (which may span
//! lines), identifiers, numbers, and the small operator set used by the
//! language. Case is not significant anywhere in the language, so keywords
//! are matched case-insensitively by the parser.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokKind {
    Ident(String),
    Number(u32),
    /// Single-character punctuation such as `( ) [ ] = , . : !`
    Symbol(char),
    /// The `->` implication arrow.
    Arrow,
    /// The `&&` conjunction operator.
    And,
    /// The `||` disjunction operator.
    Or,
    Newline,
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokKind,
    /// 1-based line number.
    pub line: usize,
    /// 1-based column number (start of token).
    pub col: usize,
}

/// A lexing error, reported with a position.
#[derive(Debug, Clone)]
pub struct LexError {
    pub line: usize,
    pub col: usize,
    pub msg: String,
}

pub fn tokenize(src: &str) -> Result<Vec<Token>, LexError> {
    let bytes: Vec<char> = src.chars().collect();
    let mut toks = Vec::new();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;

    while i < bytes.len() {
        let c = bytes[i];

        if c == '\n' {
            toks.push(Token { kind: TokKind::Newline, line, col });
            i += 1;
            line += 1;
            col = 1;
            continue;
        }

        // Whitespace (space, tab, \r) is insignificant.
        if c == ' ' || c == '\t' || c == '\r' {
            i += 1;
            col += 1;
            continue;
        }

        // Comments.
        if c == '/' && i + 1 < bytes.len() && bytes[i + 1] == '/' {
            // Line comment: skip to end of line.
            while i < bytes.len() && bytes[i] != '\n' {
                i += 1;
                col += 1;
            }
            continue;
        }
        if c == '/' && i + 1 < bytes.len() && bytes[i + 1] == '*' {
            let start_line = line;
            let start_col = col;
            i += 2;
            col += 2;
            let mut closed = false;
            while i < bytes.len() {
                if bytes[i] == '*' && i + 1 < bytes.len() && bytes[i + 1] == '/' {
                    i += 2;
                    col += 2;
                    closed = true;
                    break;
                }
                if bytes[i] == '\n' {
                    i += 1;
                    line += 1;
                    col = 1;
                } else {
                    i += 1;
                    col += 1;
                }
            }
            if !closed {
                return Err(LexError {
                    line: start_line,
                    col: start_col,
                    msg: "unterminated block comment".into(),
                });
            }
            continue;
        }

        // Multi-char operators.
        if c == '-' && i + 1 < bytes.len() && bytes[i + 1] == '>' {
            toks.push(Token { kind: TokKind::Arrow, line, col });
            i += 2;
            col += 2;
            continue;
        }
        if c == '&' && i + 1 < bytes.len() && bytes[i + 1] == '&' {
            toks.push(Token { kind: TokKind::And, line, col });
            i += 2;
            col += 2;
            continue;
        }
        if c == '|' && i + 1 < bytes.len() && bytes[i + 1] == '|' {
            toks.push(Token { kind: TokKind::Or, line, col });
            i += 2;
            col += 2;
            continue;
        }

        // Numbers.
        if c.is_ascii_digit() {
            let start_col = col;
            let mut val: u32 = 0;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                val = val * 10 + (bytes[i] as u32 - '0' as u32);
                i += 1;
                col += 1;
            }
            toks.push(Token { kind: TokKind::Number(val), line, col: start_col });
            continue;
        }

        // Identifiers: start with a letter, continue with letters/digits/_.
        if c.is_ascii_alphabetic() {
            let start_col = col;
            let mut s = String::new();
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == '_') {
                s.push(bytes[i]);
                i += 1;
                col += 1;
            }
            toks.push(Token { kind: TokKind::Ident(s), line, col: start_col });
            continue;
        }

        // Single-character symbols.
        if "( ) [ ] = , . : ! ? + - * / ^".contains(c) {
            toks.push(Token { kind: TokKind::Symbol(c), line, col });
            i += 1;
            col += 1;
            continue;
        }

        return Err(LexError {
            line,
            col,
            msg: format!("unexpected character '{}'", c),
        });
    }

    toks.push(Token { kind: TokKind::Eof, line, col });
    Ok(toks)
}
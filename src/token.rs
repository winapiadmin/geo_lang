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
            toks.push(Token {
                kind: TokKind::Newline,
                line,
                col,
            });
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
            toks.push(Token {
                kind: TokKind::Arrow,
                line,
                col,
            });
            i += 2;
            col += 2;
            continue;
        }
        if c == '&' && i + 1 < bytes.len() && bytes[i + 1] == '&' {
            toks.push(Token {
                kind: TokKind::And,
                line,
                col,
            });
            i += 2;
            col += 2;
            continue;
        }
        if c == '|' && i + 1 < bytes.len() && bytes[i + 1] == '|' {
            toks.push(Token {
                kind: TokKind::Or,
                line,
                col,
            });
            i += 2;
            col += 2;
            continue;
        }

        // Numbers.
        if c.is_ascii_digit() {
            let start_col = col;
            let mut val: u32 = 0;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                let digit = bytes[i] as u32 - '0' as u32;
                val = match val
                    .checked_mul(10)
                    .and_then(|v| v.checked_add(digit))
                {
                    Some(v) => v,
                    None => {
                        return Err(LexError {
                            line,
                            col,
                            msg: "number too large (maximum is u32::MAX)".to_string(),
                        });
                    }
                };
                i += 1;
                col += 1;
            }
            toks.push(Token {
                kind: TokKind::Number(val),
                line,
                col: start_col,
            });
            continue;
        }

        // Identifiers: start with a letter, continue with letters/digits/_ or hyphen.
        // Hyphen allowed for multi-char point segments like `P1-P2`.
        if c.is_ascii_alphabetic() {
            let start_col = col;
            let mut s = String::new();
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == '_' || bytes[i] == '-')
            {
                s.push(bytes[i]);
                i += 1;
                col += 1;
            }
            toks.push(Token {
                kind: TokKind::Ident(s),
                line,
                col: start_col,
            });
            continue;
        }

        // Single-character symbols.
        if "( ) [ ] = , . : ! ? + - * / ^".contains(c) {
            toks.push(Token {
                kind: TokKind::Symbol(c),
                line,
                col,
            });
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

    toks.push(Token {
        kind: TokKind::Eof,
        line,
        col,
    });

    // Merge indexed point references `P[1]` (or `P [ 1 ]`) into the single
    // identifier `P1`, so both spellings denote the same point. The `[...]`
    // brackets would otherwise be parsed as a triangle option list. Proof
    // headers (`proof[1]:`) and properties keep their own bracket syntax.
    let mut merged: Vec<Token> = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        let tok = toks[i].clone();
        if let TokKind::Ident(name) = &tok.kind {
            let lname = name.to_lowercase();
            let keyword = lname == "proof" || lname == "proofproperties";
            if !keyword
                && i + 3 < toks.len()
                && matches!(toks[i + 1].kind, TokKind::Symbol('['))
                && matches!(toks[i + 2].kind, TokKind::Number(_))
                && matches!(toks[i + 3].kind, TokKind::Symbol(']'))
            {
                if let TokKind::Number(n) = toks[i + 2].kind {
                    merged.push(Token {
                        kind: TokKind::Ident(format!("{}{}", name, n)),
                        line: tok.line,
                        col: tok.col,
                    });
                    i += 4;
                    continue;
                }
            }
        }
        merged.push(tok);
        i += 1;
    }
    Ok(merged)
}

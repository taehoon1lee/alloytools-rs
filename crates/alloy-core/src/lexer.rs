//! Port of `edu.mit.csail.sdg.parser` `Alloy.lex` (JFlex `CompLexer`).
//!
//! Like JFlex, every token is the longest match; on a tie the rule listed earlier in Alloy.lex wins.
//! Token kinds mirror the `CompSym` constants. Positions are 1-based (line, col) like Java's `Pos`.
//! Special-token merging (`NOTEQUALS`, `ONE_ARROW_ONE`, `ALL2`, ...) is done by the parser's filter in
//! Java, so it is NOT done here: `!=` lexes as `Not` `Equals`, exactly as the Java lexer emits it.

use crate::error::{AlloyError, Pos};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    // literals / identifiers
    Id(String),
    Num(i32),
    Str(String),
    // symbols (several spellings may map to one kind, e.g. "!" and "not")
    Not,
    Hash,
    And,
    Ampersand,
    LParen,
    RParen,
    Star,
    PlusPlus,
    Plus,
    Comma,
    Arrow,
    Minus,
    Dot,
    Slash,
    Range,
    Colon,
    Iff,
    Lte,
    Domain,
    Shl,
    Lt,
    Implies,
    Equals,
    Shr,
    Sha,
    Gte,
    Gt,
    At,
    LBracket,
    RBracket,
    Caret,
    LBrace,
    RBrace,
    Or,
    Bar,
    Tilde,
    Prime,
    TrcSeq,
    // keywords
    Abstract,
    All,
    As,
    Assert,
    But,
    Check,
    Disj,
    Else,
    Enum,
    Exactly,
    Expect,
    Extends,
    Fact,
    For,
    Fun,
    Iden,
    SigInt,
    Int,
    In,
    Let,
    Lone,
    Module,
    NoneKw,
    No,
    One,
    Open,
    Pred,
    Private,
    Run,
    Seq,
    Set,
    Sig,
    SomeKw,
    StringKw,
    Sum,
    This,
    Univ,
    Always,
    After,
    Eventually,
    Historically,
    Before,
    Once,
    Releases,
    Until,
    Since,
    Triggered,
    Var,
    Time,
    Eof,
}

/// One token with the position of its first character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub tok: Tok,
    pub line: i32,
    pub col: i32,
}

/// Punctuation/operator spellings (Alloy.lex rules whose text is not a word).
const SYMBOLS: &[(&str, Tok)] = &[
    ("!", Tok::Not),
    ("#", Tok::Hash),
    ("&&", Tok::And),
    ("&", Tok::Ampersand),
    ("(", Tok::LParen),
    (")", Tok::RParen),
    ("*", Tok::Star),
    ("++", Tok::PlusPlus),
    ("+", Tok::Plus),
    (",", Tok::Comma),
    ("->", Tok::Arrow),
    ("-", Tok::Minus),
    (".", Tok::Dot),
    ("/", Tok::Slash),
    ("::", Tok::Dot),
    (":>", Tok::Range),
    (":", Tok::Colon),
    ("<=>", Tok::Iff),
    ("<=", Tok::Lte),
    ("<:", Tok::Domain),
    ("<<", Tok::Shl),
    ("<", Tok::Lt),
    ("=<", Tok::Lte),
    ("=>", Tok::Implies),
    ("=", Tok::Equals),
    (">>>", Tok::Shr),
    (">>", Tok::Sha),
    (">=", Tok::Gte),
    (">", Tok::Gt),
    ("@", Tok::At),
    ("[", Tok::LBracket),
    ("]", Tok::RBracket),
    ("^", Tok::Caret),
    ("{", Tok::LBrace),
    ("||", Tok::Or),
    ("|", Tok::Bar),
    ("}", Tok::RBrace),
    ("~", Tok::Tilde),
    (";", Tok::TrcSeq),
    ("'", Tok::Prime),
    ("\u{2018}", Tok::Prime),
    ("\u{2019}", Tok::Prime),
];

/// Word rules (keywords). Identifiers that equal one of these become the keyword token.
fn keyword(word: &str) -> Option<Tok> {
    Some(match word {
        "abstract" => Tok::Abstract,
        "all" => Tok::All,
        "and" => Tok::And,
        "assert" => Tok::Assert,
        "as" => Tok::As,
        "but" => Tok::But,
        "check" => Tok::Check,
        "disj" => Tok::Disj,
        "else" => Tok::Else,
        "enum" => Tok::Enum,
        "exactly" => Tok::Exactly,
        "expect" => Tok::Expect,
        "extends" => Tok::Extends,
        "fact" => Tok::Fact,
        "for" => Tok::For,
        "fun" => Tok::Fun,
        "iden" => Tok::Iden,
        "iff" => Tok::Iff,
        "implies" => Tok::Implies,
        "Int" => Tok::SigInt,
        "int" => Tok::Int,
        "in" => Tok::In,
        "let" => Tok::Let,
        "lone" => Tok::Lone,
        "module" => Tok::Module,
        "none" => Tok::NoneKw,
        "not" => Tok::Not,
        "no" => Tok::No,
        "one" => Tok::One,
        "open" => Tok::Open,
        "or" => Tok::Or,
        "pred" => Tok::Pred,
        "private" => Tok::Private,
        "run" => Tok::Run,
        "seq" => Tok::Seq,
        "set" => Tok::Set,
        "sig" => Tok::Sig,
        "some" => Tok::SomeKw,
        "String" => Tok::StringKw,
        "sum" => Tok::Sum,
        "this" => Tok::This,
        "univ" => Tok::Univ,
        "always" => Tok::Always,
        "after" => Tok::After,
        "eventually" => Tok::Eventually,
        "historically" => Tok::Historically,
        "before" => Tok::Before,
        "once" => Tok::Once,
        "releases" => Tok::Releases,
        "until" => Tok::Until,
        "since" => Tok::Since,
        "triggered" => Tok::Triggered,
        "var" => Tok::Var,
        "steps" => Tok::Time,
        _ => return None,
    })
}

/// `[:jletter:]` (Java identifier start) approximation.
fn is_id_start(c: char) -> bool {
    c.is_alphabetic() || c == '$' || c == '_'
}

/// `[:jletterdigit:]\"` — identifier continuation; note the `"` is part of identifiers in Alloy.
fn is_id_part(c: char) -> bool {
    c.is_alphanumeric() || c == '$' || c == '_' || c == '"'
}

/// Character class `[\$0-9a-zA-Z_\"]` used by the "name cannot start with a number" rule.
fn is_ascii_name_part(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '$' || c == '_' || c == '"'
}

fn is_ascii_name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '$' || c == '_' || c == '"'
}

/// Lex `src` (the contents of file `file`). Returns the tokens without a trailing EOF token,
/// or the first lexical error (`ErrorKind::Syntax`), like Java's `ErrorSyntax` thrown by the lexer.
pub fn lex(file: &str, src: &str) -> Result<Vec<Token>, AlloyError> {
    let chars: Vec<char> = src.chars().collect();
    let mut lx = Lexer { file, cs: &chars, i: 0, line: 1, col: 1 };
    let mut out = Vec::new();
    while lx.i < chars.len() {
        let c = chars[lx.i];
        if matches!(c, ' ' | '\t' | '\u{0C}' | '\r' | '\n') {
            lx.advance(1);
        } else if lx.starts_with("//") || lx.starts_with("--") {
            // line comment: up to (not including) the line terminator
            while lx.i < chars.len() && !matches!(chars[lx.i], '\r' | '\n') {
                lx.advance(1);
            }
        } else if lx.starts_with("/*") && lx.block_comment_end().is_some() {
            let end = lx.block_comment_end().unwrap_or(chars.len());
            lx.advance(end - lx.i);
        } else if c == '"' {
            out.push(lx.string()?);
        } else if c.is_ascii_digit() {
            out.push(lx.number()?);
        } else if is_id_start(c) {
            out.push(lx.word());
        } else if let Some((len, tok)) = lx.symbol() {
            let (line, col) = (lx.line, lx.col);
            lx.advance(len);
            out.push(Token { tok, line, col });
        } else {
            return Err(lx.err(&format!(
                "Syntax error at the {c} character. HEX: \\u{:x})",
                c as u32
            )));
        }
    }
    Ok(out)
}

struct Lexer<'a> {
    file: &'a str,
    cs: &'a [char],
    i: usize,
    line: i32,
    col: i32,
}

impl<'a> Lexer<'a> {
    fn starts_with(&self, s: &str) -> bool {
        let mut k = self.i;
        for ch in s.chars() {
            if self.cs.get(k) != Some(&ch) {
                return false;
            }
            k += 1;
        }
        true
    }

    fn at(&self, k: usize) -> Option<char> {
        self.cs.get(self.i + k).copied()
    }

    fn err(&self, msg: &str) -> AlloyError {
        AlloyError::syntax(
            Pos { file: self.file.to_string(), line: self.line, col: self.col },
            msg,
        )
    }

    /// Consume `n` characters, maintaining line/column like JFlex `%line %column`.
    fn advance(&mut self, n: usize) {
        for _ in 0..n {
            let c = self.cs[self.i];
            self.i += 1;
            match c {
                '\r' => {
                    if self.cs.get(self.i) == Some(&'\n') {
                        self.col += 1;
                    } else {
                        self.newline();
                    }
                }
                '\n' | '\u{0B}' | '\u{0C}' | '\u{85}' | '\u{2028}' | '\u{2029}' => self.newline(),
                _ => self.col += 1,
            }
        }
    }

    fn newline(&mut self) {
        self.line += 1;
        self.col = 1;
    }

    /// Index just past the `*/` closing a block comment that starts at `self.i`, if any.
    fn block_comment_end(&self) -> Option<usize> {
        let mut k = self.i + 2;
        while k + 1 < self.cs.len() {
            if self.cs[k] == '*' && self.cs[k + 1] == '/' {
                return Some(k + 2);
            }
            k += 1;
        }
        None
    }

    /// Longest punctuation match at the current position.
    fn symbol(&self) -> Option<(usize, Tok)> {
        let mut best: Option<(usize, Tok)> = None;
        for (text, tok) in SYMBOLS {
            let n = text.chars().count();
            if self.starts_with(text) && best.as_ref().map_or(true, |(b, _)| n > *b) {
                best = Some((n, tok.clone()));
            }
        }
        best
    }

    /// Identifier or keyword (`[:jletter:][[:jletterdigit:]\"]*` vs the keyword rules).
    fn word(&mut self) -> Token {
        let (line, col) = (self.line, self.col);
        let start = self.i;
        while self.at(0).is_some_and(is_id_part) {
            self.advance(1);
        }
        let text: String = self.cs[start..self.i].iter().collect();
        let tok = keyword(&text).unwrap_or(Tok::Id(text));
        Token { tok, line, col }
    }

    /// String literal (`"..."` with escapes `\n`, `\"`, `\\`).
    fn string(&mut self) -> Result<Token, AlloyError> {
        let (line, col) = (self.line, self.col);
        let start = self.i;
        let mut j = self.i + 1;
        loop {
            match self.cs.get(j) {
                None => {
                    return Err(self.err("String literal is missing its closing \" character"));
                }
                Some('\\') => j += 2,
                Some('"') => break,
                Some(_) => j += 1,
            }
        }
        let end = j + 1;
        if self.cs.get(end).is_some_and(|&c| is_ascii_name_part(c)) {
            return Err(self.err("String literal cannot be followed by a legal identifier character."));
        }
        // Java `alloy_string` validation of the raw text (quotes included).
        let raw: Vec<char> = self.cs[start..end].to_vec();
        let mut value = String::new();
        let mut k = 0;
        while k < raw.len() {
            let mut c = raw[k];
            if c == '\r' || c == '\n' {
                return Err(self.err("String literal cannot span multiple lines; use \\n instead."));
            }
            if c == '\\' {
                k += 1;
                match raw.get(k) {
                    None => return Err(self.err("String literal cannot end with a single \\")),
                    Some('n') => c = '\n',
                    Some(&other) if other != '"' && other != '\\' => {
                        return Err(self.err(
                            "String literal currently only supports\nthree escape sequences: \\\\, \\n, and \\\"",
                        ));
                    }
                    Some(&other) => c = other,
                }
            }
            value.push(c);
            k += 1;
        }
        // `value` still contains the two quote characters, as in Java; empty means `""`.
        if value.chars().count() == 2 {
            return Err(self.err(
                "Empty string is not allowed; try rewriting your model to use an empty set instead.",
            ));
        }
        let inner: String = value.chars().skip(1).take(value.chars().count() - 2).collect();
        self.advance(end - start);
        Ok(Token { tok: Tok::Str(inner), line, col })
    }

    /// Numbers: decimal, `0x` hex, `0b` binary, and the "name cannot start with a number" error.
    /// Longest match wins; ties resolved in Alloy.lex rule order (hex, binary, name, decimal).
    fn number(&mut self) -> Result<Token, AlloyError> {
        let (line, col) = (self.line, self.col);
        let base = self.i;
        let cs = self.cs;
        let at = |k: usize| cs.get(base + k).copied();

        // candidate lengths; index 0..=3 = hex, binary, name, decimal
        let mut run = 0;
        while at(run).is_some_and(is_ascii_name_part) {
            run += 1;
        }
        let name_ok = (0..run).any(|k| at(k).is_some_and(is_ascii_name_start));
        let mut dec = 0;
        while at(dec).is_some_and(|c| c.is_ascii_digit() || c == '_') {
            dec += 1;
        }
        let mut hex = 0;
        if at(0) == Some('0') && at(1) == Some('x') {
            let mut j = 2;
            loop {
                if at(j) == Some('_') {
                    j += 1;
                } else if at(j).is_some_and(|c| c.is_ascii_hexdigit()) && at(j + 1).is_some_and(|c| c.is_ascii_hexdigit()) {
                    j += 2;
                } else {
                    break;
                }
            }
            if j > 2 {
                hex = j;
            }
        }
        let mut bin = 0;
        if at(0) == Some('0') && at(1) == Some('b') {
            let mut j = 2;
            while at(j).is_some_and(|c| c == '0' || c == '1' || c == '_') {
                j += 1;
            }
            if j > 2 {
                bin = j;
            }
        }

        let mut best = (0usize, 0u8);
        for (kind, len, ok) in [(0u8, hex, true), (1, bin, true), (2, run, name_ok), (3, dec, true)] {
            if ok && len > best.0 {
                best = (len, kind);
            }
        }
        let (len, kind) = best;
        let text: String = cs[base..base + len].iter().collect();
        let pos = self.pos_at(line, col);
        let value = match kind {
            2 => return Err(AlloyError::syntax(pos, "Name cannot start with a number.")),
            0 => parse_radix(&text[2..], 16, &pos)?,
            1 => parse_radix(&text[2..], 2, &pos)?,
            _ => parse_radix(&text, 10, &pos)?,
        };
        self.advance(len);
        Ok(Token { tok: Tok::Num(value), line, col })
    }

    fn pos_at(&self, line: i32, col: i32) -> Pos {
        Pos { file: self.file.to_string(), line, col }
    }
}

/// Java `Integer.parseInt` after removing `_`; any failure is a syntax error at the token.
fn parse_radix(digits: &str, radix: u32, pos: &Pos) -> Result<i32, AlloyError> {
    let clean: String = digits.chars().filter(|&c| c != '_').collect();
    i32::from_str_radix(&clean, radix)
        .map_err(|e| AlloyError::syntax(pos.clone(), format!("The number {clean} {e}")))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(src: &str) -> Vec<Tok> {
        lex("t.als", src).expect("lex ok").into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn operators_longest_match() {
        assert_eq!(toks("<=> <= =< => < <: << >>> >> >= > :> :: :"), vec![
            Tok::Iff, Tok::Lte, Tok::Lte, Tok::Implies, Tok::Lt, Tok::Domain, Tok::Shl, Tok::Shr, Tok::Sha,
            Tok::Gte, Tok::Gt, Tok::Range, Tok::Dot, Tok::Colon,
        ]);
        assert_eq!(toks("!= !in ++ + -> - || |"), vec![
            Tok::Not, Tok::Equals, Tok::Not, Tok::In, Tok::PlusPlus, Tok::Plus, Tok::Arrow, Tok::Minus, Tok::Or, Tok::Bar,
        ]);
    }

    #[test]
    fn keywords_vs_identifiers() {
        assert_eq!(toks("all allx Int int steps a_b' x\"y"), vec![
            Tok::All,
            Tok::Id("allx".into()),
            Tok::SigInt,
            Tok::Int,
            Tok::Time,
            Tok::Id("a_b".into()),
            Tok::Prime,
            Tok::Id("x\"y".into()),
        ]);
        assert_eq!(toks("and or iff implies not"), vec![Tok::And, Tok::Or, Tok::Iff, Tok::Implies, Tok::Not]);
    }

    #[test]
    fn numbers() {
        assert_eq!(toks("42 100 0x1F 0xab_cd 0b1_01"), vec![
            Tok::Num(42), Tok::Num(100), Tok::Num(0x1f), Tok::Num(0xabcd), Tok::Num(5),
        ]);
        // Alloy.lex quirk: "1_000" matches both the decimal rule and the "name cannot start with a
        // number" rule with equal length; the earlier rule (the name error) wins.
        assert!(lex("t.als", "1_000").is_err());
        assert!(lex("t.als", "0xa_b").is_err());
        assert!(lex("t.als", "1abc").is_err());
        assert!(lex("t.als", "0xg").is_err());
    }

    #[test]
    fn comments_and_positions() {
        let v = lex("t.als", "// c\n-- d\n/* x */ a /** y\n */ b\n  c").unwrap();
        assert_eq!(v.iter().map(|t| (t.tok.clone(), t.line, t.col)).collect::<Vec<_>>(), vec![
            (Tok::Id("a".into()), 3, 9),
            (Tok::Id("b".into()), 4, 5),
            (Tok::Id("c".into()), 5, 3),
        ]);
    }

    #[test]
    fn strings() {
        assert_eq!(toks(r#""a\"b\n""#), vec![Tok::Str("a\"b\n".into())]);
        assert!(lex("t.als", "\"\"").is_err());
        assert!(lex("t.als", "\"abc").is_err());
        assert!(lex("t.als", "\"abc\"x").is_err());
        assert!(lex("t.als", "\"a\\q\"").is_err());
    }

    #[test]
    fn bad_character_is_syntax_error() {
        let e = lex("t.als", "a \u{1}").unwrap_err();
        assert_eq!(e.kind, crate::error::ErrorKind::Syntax);
        let p = e.pos.as_ref().expect("position");
        assert_eq!((p.line, p.col), (1, 3));
    }

    #[test]
    fn every_corpus_file_lexes() {
        fn walk(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
            let Ok(rd) = std::fs::read_dir(dir) else { return };
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() {
                    walk(&p, out);
                } else if p.extension().is_some_and(|x| x == "als") {
                    out.push(p);
                }
            }
        }
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reference");
        let mut files = Vec::new();
        walk(&root, &mut files);
        assert!(!files.is_empty(), "no .als files found under {}", root.display());
        let mut failures = Vec::new();
        for f in &files {
            let src = std::fs::read_to_string(f).unwrap_or_default();
            if let Err(e) = lex(&f.display().to_string(), &src) {
                failures.push(format!("{e}"));
            }
        }
        assert!(failures.is_empty(), "{} files failed to lex:\n{}", failures.len(), failures.join("\n"));
    }
}

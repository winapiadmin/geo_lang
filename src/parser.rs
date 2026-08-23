//! Recursive-descent parser for `.geo` files.

use crate::ast::*;
use crate::claim::{RatioAtom, RatioExpr, Value};
use crate::token::{TokKind, Token};

/// A parse error.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub pos: Pos,
    pub msg: String,
}

type Toks = Vec<Token>;

pub fn parse(source: &str, src_text: &str) -> Result<File, ParseError> {
    let toks = crate::token::tokenize(src_text).map_err(|e| ParseError {
        pos: Pos {
            line: e.line,
            col: e.col,
        },
        msg: e.msg,
    })?;
    let lines: Vec<String> = src_text.lines().map(|l| l.to_string()).collect();
    Parser::new(source, lines, toks).parse_file()
}

struct Parser {
    source: String,
    lines: Vec<String>,
    toks: Toks,
}

/// A logical line of tokens (a statement).
struct Line {
    toks: Vec<Token>,
}

impl Parser {
    fn new(source: &str, lines: Vec<String>, toks: Toks) -> Parser {
        Parser {
            source: source.into(),
            lines,
            toks,
        }
    }

    fn err<T>(&self, pos: Pos, msg: &str) -> Result<T, ParseError> {
        Err(ParseError {
            pos,
            msg: msg.into(),
        })
    }

    /// Split the token stream into logical lines (statements are line-based).
    /// A line that ends with an unbalanced `(` continues on the next line, so
    /// multi-line calls such as `Intersection(\n A,\n B\n)` are one statement.
    fn split_lines(&self) -> Result<Vec<Line>, ParseError> {
        let mut out: Vec<Line> = Vec::new();
        let mut cur: Vec<Token> = Vec::new();
        let mut depth = 0usize;
        for t in &self.toks {
            match t.kind {
                TokKind::Newline | TokKind::Eof => {
                    if depth > 0 && t.kind != TokKind::Eof {
                        // Inside a call: the newline is insignificant.
                        continue;
                    }
                    if !cur.is_empty() {
                        out.push(Line {
                            toks: std::mem::take(&mut cur),
                        });
                    }
                }
                TokKind::Symbol('(') => {
                    depth += 1;
                    cur.push(t.clone());
                }
                TokKind::Symbol(')') => {
                    depth = depth.saturating_sub(1);
                    cur.push(t.clone());
                }
                _ => {
                    cur.push(t.clone());
                }
            }
        }
        Ok(out)
    }

    fn parse_file(&mut self) -> Result<File, ParseError> {
        let mut file = File {
            source: self.source.clone(),
            lines: self.lines.clone(),
            input: Vec::new(),
            goals: Vec::new(),
            props: Vec::new(),
            proofs: Vec::new(),
        };

        let lines = self.split_lines()?;
        #[derive(PartialEq)]
        enum Section {
            None,
            Input,
            Prove,
        }
        let mut section = Section::None;
        let mut in_proof: Option<ProofBlock> = None;

        for line in lines {
            if line.toks.is_empty() {
                continue;
            }
            let head = line.toks.first().map(|t| &t.kind);

            if let Some(TokKind::Ident(id)) = head {
                let low = id.to_lowercase();
                if low == "inp" || low == "input" {
                    section = Section::Input;
                    self.expect_colon(&line)?;
                    continue;
                }
                if low == "prove" {
                    section = Section::Prove;
                    self.expect_colon(&line)?;
                    continue;
                }
            }

            match section {
                Section::None => {
                    return self.err(pos_of(&line.toks[0]), "expected `inp:` or `prove:` section");
                }
                Section::Input => {
                    self.parse_input_stmt(&line, &mut file.input)?;
                }
                Section::Prove => {
                    // A new `proof[N]:` header closes the previous proof block.
                    if is_proof_header(&line) {
                        if let Some(p) = in_proof.take() {
                            file.proofs.push(p);
                        }
                        let block = self.parse_proof_header(&line)?;
                        in_proof = Some(block);
                        continue;
                    }
                    if is_proof_property(&line) {
                        if let Some(p) = in_proof.take() {
                            file.proofs.push(p);
                        }
                        let prop = self.parse_proof_prop(&line)?;
                        file.props.push(prop);
                        continue;
                    }
                    if is_goal_line(&line) {
                        if let Some(p) = in_proof.take() {
                            file.proofs.push(p);
                        }
                        let goal = self.parse_goal(&line)?;
                        file.goals.push(goal);
                        continue;
                    }
                    // A `->` continuation line extends the previous step's
                    // chain, so a proof may be written across several lines:
                    //   a -> B
                    //     -> C
                    if is_arrow_start(&line) {
                        if let Some(p) = in_proof.as_mut() {
                            self.continue_chain(p, &line)?;
                            continue;
                        }
                        return self.err(
                            pos_of(&line.toks[0]),
                            "`->` continuation outside of a proof block",
                        );
                    }
                    // Otherwise: a proof step (only valid inside a proof block).
                    if let Some(p) = in_proof.as_mut() {
                        let step = self.parse_step(&line)?;
                        p.steps.push(step);
                        continue;
                    }
                    return self.err(
                        pos_of(&line.toks[0]),
                        "statement outside of a proof block; expected `proof[N]:`, `proofProperties[...]`, or `N. claim`",
                    );
                }
            }
        }

        if let Some(p) = in_proof.take() {
            file.proofs.push(p);
        }

        Ok(file)
    }

    fn expect_colon(&self, line: &Line) -> Result<(), ParseError> {
        if line.toks.len() != 2 || !is_symbol(&line.toks[1], ':') {
            return self.err(pos_of(&line.toks[0]), "expected `:` after section header");
        }
        Ok(())
    }

    // ---- input statements ----

    fn parse_input_stmt(&self, line: &Line, out: &mut Vec<InputStmt>) -> Result<(), ParseError> {
        let t = &line.toks[0];
        let pos = pos_of(t);
        if let TokKind::Ident(id) = &t.kind {
            let low = id.to_lowercase();
            match low.as_str() {
                "triangle" => {
                    let stmt = self.parse_triangle(line)?;
                    out.push(stmt);
                    return Ok(());
                }
                "segment" => {
                    let stmt =
                        self.parse_pair_stmt(line, |a, b, pos| InputStmt::Segment { a, b, pos })?;
                    out.push(stmt);
                    return Ok(());
                }
                "line" => {
                    let stmt =
                        self.parse_pair_stmt(line, |a, b, pos| InputStmt::Line { a, b, pos })?;
                    out.push(stmt);
                    return Ok(());
                }
                "angle" => {
                    let stmt = self.parse_angle_eq(line)?;
                    out.push(stmt);
                    return Ok(());
                }
                _ => {
                    // Chained equality of length expressions, e.g. `AB=MN`
                    // or `AM=BN=CP` or `AD=3`.
                    if line.toks.len() >= 3 && is_symbol(&line.toks[1], '=') {
                        let mut is_eq = false;
                        if let TokKind::Ident(rhs) = &line.toks[2].kind {
                            if !is_construction_word(rhs) {
                                is_eq = true;
                            }
                        }
                        if matches!(line.toks[2].kind, TokKind::Number(_)) {
                            is_eq = true;
                        }
                        if is_eq {
                            let toks = &line.toks;
                            let mut k = 0usize;
                            let mut items = vec![self.parse_len_expr(toks, &mut k)?];
                            self.parse_eq_chain_rest(toks, &mut k, &mut items)?;
                            if k != toks.len() {
                                return self.err(pos_of(&toks[k]), "unexpected tokens in equality");
                            }
                            out.push(InputStmt::EqChain { items, pos });
                            return Ok(());
                        }
                    }
                    // Assignment: `D = Intersection(...)`.
                    if line.toks.len() >= 3 && is_symbol(&line.toks[1], '=') {
                        let name = id.clone();
                        let mut rest = line.toks[2..].to_vec();
                        let geom = self.parse_geom(&mut rest)?;
                        if !rest.is_empty() {
                            return self.err(pos_of(&rest[0]), "unexpected tokens in assignment");
                        }
                        out.push(InputStmt::Assign { name, geom, pos });
                        return Ok(());
                    }
                    // Ratio equality: `BD/DC = AB/AC`.
                    if line.toks.len() >= 3 && is_symbol(&line.toks[1], '/') {
                        let toks = &line.toks;
                        let mut k = 0usize;
                        let lhs = self.parse_ratio_expr(toks, &mut k)?;
                        expect_symbol(toks, &mut k, '=')?;
                        let rhs = self.parse_ratio_expr(toks, &mut k)?;
                        if k != toks.len() {
                            return self
                                .err(pos_of(&toks[k]), "unexpected tokens in ratio equality");
                        }
                        out.push(InputStmt::RatioEq { lhs, rhs, pos });
                        return Ok(());
                    }
                    // Predicate fact: `Name(args)=value` or `Name(args)`.
                    if line.toks.len() >= 3 && is_symbol(&line.toks[1], '(') {
                        let toks = &line.toks;
                        let mut k = 0usize;
                        let atom = self.parse_claim_atom(toks, &mut k)?;
                        if k != toks.len() {
                            return self
                                .err(pos_of(&toks[k]), "unexpected tokens in predicate fact");
                        }
                        let stmt = match atom {
                            ClaimExpr::PredEq {
                                name,
                                args,
                                value,
                                pos,
                            } => InputStmt::PredFact {
                                name,
                                args,
                                value,
                                pos,
                            },
                            ClaimExpr::PredCall { name, args, pos } => InputStmt::PredFact {
                                name,
                                args,
                                value: Value::Bool(true),
                                pos,
                            },
                            ClaimExpr::EqChain { items, pos } => InputStmt::EqChain { items, pos },
                            other => {
                                return self.err(
                                    pos_of(&line.toks[0]),
                                    &format!("cannot use `{:?}` as an input fact", other),
                                );
                            }
                        };
                        out.push(stmt);
                        return Ok(());
                    }
                }
            }
        }
        self.err(
            pos,
            "expected a Triangle, Segment, Line, or `name = ...` construction",
        )
    }

    fn parse_triangle(&self, line: &Line) -> Result<InputStmt, ParseError> {
        let pos = pos_of(&line.toks[0]);
        let toks = &line.toks;
        let mut k = 1;
        expect_symbol(toks, &mut k, '(')?;
        let mut points = Vec::new();
        while k < toks.len() && !is_symbol(&toks[k], ')') && !is_symbol(&toks[k], '[') {
            let p = expect_ident(toks, &mut k)?.clone();
            points.push(p);
            if k < toks.len() && is_symbol(&toks[k], ',') {
                k += 1;
            }
        }
        let name = points.join("");
        let mut props = Vec::new();
        if k < toks.len() && is_symbol(&toks[k], ',') {
            k += 1;
        }
        if k < toks.len() && is_symbol(&toks[k], '[') {
            k += 1;
            while k < toks.len() && !is_symbol(&toks[k], ']') {
                let pname = expect_ident(toks, &mut k)?.to_lowercase();
                expect_symbol(toks, &mut k, '=')?;
                let val = parse_value_at(toks, &mut k)?;
                props.push((pname, val));
                if k < toks.len() && is_symbol(&toks[k], ',') {
                    k += 1;
                }
            }
            expect_symbol(toks, &mut k, ']')?;
        }
        expect_symbol(toks, &mut k, ')')?;
        if k != toks.len() {
            return self.err(
                pos_of(&toks[k]),
                "unexpected tokens in Triangle declaration",
            );
        }
        Ok(InputStmt::Triangle {
            name,
            points,
            props,
            pos,
        })
    }

    fn parse_pair_stmt<F>(&self, line: &Line, make: F) -> Result<InputStmt, ParseError>
    where
        F: Fn(String, String, Pos) -> InputStmt,
    {
        let pos = pos_of(&line.toks[0]);
        let toks = &line.toks;
        let mut k = 1;
        expect_symbol(toks, &mut k, '(')?;
        let a = expect_ident(toks, &mut k)?.clone();
        expect_symbol(toks, &mut k, ',')?;
        let b = expect_ident(toks, &mut k)?.clone();
        expect_symbol(toks, &mut k, ')')?;
        if k != toks.len() {
            return self.err(pos_of(&toks[k]), "unexpected tokens");
        }
        Ok(make(a, b, pos))
    }

    /// Parse an angle equality in the input section, e.g.
    /// `Angle(ABC) = Angle(MNP)`.
    fn parse_angle_eq(&self, line: &Line) -> Result<InputStmt, ParseError> {
        let pos = pos_of(&line.toks[0]);
        let toks = &line.toks;
        let mut k = 1;
        expect_symbol(toks, &mut k, '(')?;
        let lhs = expect_ident(toks, &mut k)?.to_lowercase();
        expect_symbol(toks, &mut k, ')')?;
        expect_symbol(toks, &mut k, '=')?;
        if !is_ident_word(&toks[k], "angle") {
            return self.err(pos_of(&toks[k]), "expected `Angle`");
        }
        k += 1;
        expect_symbol(toks, &mut k, '(')?;
        let rhs = expect_ident(toks, &mut k)?.to_lowercase();
        expect_symbol(toks, &mut k, ')')?;
        if k != toks.len() {
            return self.err(pos_of(&toks[k]), "unexpected tokens in angle equality");
        }
        Ok(InputStmt::AngleEq { lhs, rhs, pos })
    }

    fn parse_geom(&self, toks: &mut Vec<Token>) -> Result<Geom, ParseError> {
        let t = toks.first().cloned().ok_or(ParseError {
            pos: Pos { line: 0, col: 0 },
            msg: "expected a construction".into(),
        })?;
        let pos = pos_of(&t);
        if let TokKind::Ident(id) = &t.kind {
            let low = id.to_lowercase();
            match low.as_str() {
                "intersection" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let mut geoms = Vec::new();
                    geoms.push(self.parse_geom(toks)?);
                    while toks.first().map(|t| is_symbol(t, ',')).unwrap_or(false) {
                        toks.remove(0);
                        geoms.push(self.parse_geom(toks)?);
                    }
                    expect_first_symbol(toks, ')')?;
                    if geoms.len() < 2 {
                        return self.err(pos, "Intersection requires more than 1 segment or line");
                    }
                    Ok(Geom::Intersection(geoms, pos))
                }
                "perpendicularline" | "prependicularline" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let point = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ',')?;
                    let base = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ')')?;
                    Ok(Geom::PerpendicularLine { point, base, pos })
                }
                "parallelline" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let point = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ',')?;
                    let base = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ')')?;
                    Ok(Geom::ParallelLine { point, base, pos })
                }
                "midpoint" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let first = expect_first_ident(toks)?;
                    if toks.first().map(|t| is_symbol(t, ',')).unwrap_or(false) {
                        // Midpoint(A, B): two endpoint points.
                        expect_first_symbol(toks, ',')?;
                        let b = expect_first_ident(toks)?;
                        expect_first_symbol(toks, ')')?;
                        Ok(Geom::Midpoint { a: first, b, pos })
                    } else {
                        // Midpoint(BC): a single segment reference, split
                        // into its two endpoint points.
                        expect_first_symbol(toks, ')')?;
                        let names = crate::claim::Claim::split_ref_names(&first);
                        if names.len() != 2 {
                            return self.err(pos, "Midpoint(Segment) requires a two-point segment such as `Midpoint(BC)`");
                        }
                        Ok(Geom::Midpoint {
                            a: names[0].clone(),
                            b: names[1].clone(),
                            pos,
                        })
                    }
                }
                "anglebisector" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let vertex = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ',')?;
                    let base = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ')')?;
                    Ok(Geom::AngleBisector { vertex, base, pos })
                }
                "altitude" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let vertex = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ',')?;
                    let base = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ')')?;
                    Ok(Geom::Altitude { vertex, base, pos })
                }
                "pointon" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let inner = self.parse_geom(toks)?;
                    expect_first_symbol(toks, ')')?;
                    match inner {
                        Geom::Ref(r) => Ok(Geom::PointOn { seg: r, line_pts: None, pos }),
                        Geom::Line { a, b, .. } => Ok(Geom::PointOn {
                            seg: format!("{}{}", a, b),
                            line_pts: Some((a, b)),
                            pos,
                        }),
                        _ => self.err(
                            pos,
                            "PointOn expects a segment or a line, e.g. `PointOn(AB)` or `PointOn(Line(A,B))`",
                        ),
                    }
                }
                "line" | "segment" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let a = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ',')?;
                    let b = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ')')?;
                    Ok(Geom::Line { a, b, pos })
                }
                "circumcenter" | "incenter" | "orthocenter" | "centroid" => {
                    toks.remove(0);
                    expect_first_symbol(toks, '(')?;
                    let tri = expect_first_ident(toks)?;
                    expect_first_symbol(toks, ')')?;
                    let kind = match low.as_str() {
                        "circumcenter" => CenterKind::Circumcenter,
                        "incenter" => CenterKind::Incenter,
                        "orthocenter" => CenterKind::Orthocenter,
                        _ => CenterKind::Centroid,
                    };
                    Ok(Geom::Center { kind, tri, pos })
                }
                _ => {
                    toks.remove(0);
                    Ok(Geom::Ref(id.to_lowercase()))
                }
            }
        } else {
            self.err(pos, "expected an identifier or construction")
        }
    }

    // ---- prove section ----

    fn parse_goal(&self, line: &Line) -> Result<Goal, ParseError> {
        let pos = pos_of(&line.toks[0]);
        let toks = &line.toks;
        let mut k = 0;
        let index = match &toks[k].kind {
            TokKind::Number(n) => *n,
            _ => return self.err(pos, "expected goal number"),
        };
        k += 1;
        expect_symbol(toks, &mut k, '.')?;
        if k < toks.len() && is_ident_word(&toks[k], "nothing") {
            if k + 1 != toks.len() {
                return self.err(pos_of(&toks[k + 1]), "unexpected tokens after `Nothing`");
            }
            return Ok(Goal {
                index,
                claim: None,
                pos,
            });
        }
        let mut claims = Vec::new();
        self.parse_chain(toks, &mut k, &mut claims)?;
        if k != toks.len() {
            return self.err(pos_of(&toks[k]), "unexpected tokens after goal");
        }
        if claims.len() != 1 {
            return self.err(pos, "a goal must be a single claim");
        }
        Ok(Goal {
            index,
            claim: Some(claims[0].clone()),
            pos,
        })
    }

    fn parse_proof_prop(&self, line: &Line) -> Result<ProofProp, ParseError> {
        let pos = pos_of(&line.toks[0]);
        let toks = &line.toks;
        let mut k = 0;
        if !is_ident_word(&toks[k], "proofproperties") {
            return self.err(pos, "expected `proofProperties`");
        }
        k += 1;
        expect_symbol(toks, &mut k, '[')?;
        let index = match &toks[k].kind {
            TokKind::Number(n) => *n,
            _ => return self.err(pos_of(&toks[k]), "expected proof index"),
        };
        k += 1;
        expect_symbol(toks, &mut k, ']')?;
        expect_symbol(toks, &mut k, '[')?;
        if !is_ident_word(&toks[k], "scope") {
            return self.err(pos_of(&toks[k]), "expected `Scope` property");
        }
        k += 1;
        expect_symbol(toks, &mut k, ']')?;
        expect_symbol(toks, &mut k, '=')?;
        let scope = if is_ident_word(&toks[k], "local") {
            Scope::Local
        } else if is_ident_word(&toks[k], "global") {
            Scope::Global
        } else {
            return self.err(pos_of(&toks[k]), "expected `Local` or `Global`");
        };
        k += 1;
        if k != toks.len() {
            return self.err(pos_of(&toks[k]), "unexpected tokens");
        }
        Ok(ProofProp { index, scope, pos })
    }

    fn parse_proof_header(&self, line: &Line) -> Result<ProofBlock, ParseError> {
        let pos = pos_of(&line.toks[0]);
        let toks = &line.toks;
        let mut k = 0;
        if !is_ident_word(&toks[k], "proof") {
            return self.err(pos, "expected `proof`");
        }
        k += 1;
        expect_symbol(toks, &mut k, '[')?;
        let index = match &toks[k].kind {
            TokKind::Number(n) => *n,
            _ => return self.err(pos_of(&toks[k]), "expected proof index"),
        };
        k += 1;
        expect_symbol(toks, &mut k, ']')?;
        expect_symbol(toks, &mut k, ':')?;
        if k != toks.len() {
            return self.err(pos_of(&toks[k]), "unexpected tokens after proof header");
        }
        Ok(ProofBlock {
            index,
            steps: Vec::new(),
            pos,
        })
    }

    fn parse_step(&self, line: &Line) -> Result<Step, ParseError> {
        let pos = pos_of(&line.toks[0]);
        if line.toks.len() == 1 && is_ident_word(&line.toks[0], "nothing") {
            return Ok(Step::Nothing(pos));
        }
        let mut claims = Vec::new();
        let mut k = 0;
        self.parse_chain(&line.toks, &mut k, &mut claims)?;
        if k != line.toks.len() {
            return self.err(pos_of(&line.toks[k]), "unexpected tokens after proof step");
        }
        Ok(Step::Chain { claims, pos })
    }

    /// Extend the previous step's chain with the claims after a leading `->`,
    /// so multi-line proofs like `a -> B` / `  -> C` form one chain.
    fn continue_chain(&self, block: &mut ProofBlock, line: &Line) -> Result<(), ParseError> {
        let last = match block.steps.pop() {
            Some(s) => s,
            None => return self.err(pos_of(&line.toks[0]), "`->` continuation with no preceding step"),
        };
        match last {
            Step::Chain { mut claims, pos } => {
                let toks = &line.toks;
                let mut k = 1; // skip the leading `->`
                if k >= toks.len() {
                    return self.err(pos_of(&toks[0]), "`->` continuation needs a claim");
                }
                self.parse_chain(toks, &mut k, &mut claims)?;
                if k != toks.len() {
                    return self.err(pos_of(&toks[k]), "unexpected tokens after proof step");
                }
                block.steps.push(Step::Chain { claims, pos });
                Ok(())
            }
            Step::Nothing(_) => {
                self.err(pos_of(&line.toks[0]), "`->` continuation cannot follow `Nothing`")
            }
        }
    }

    // ---- claims ----

    /// Parse `claim (-> claim)*` from `toks`, starting at `*k`.
    fn parse_chain(
        &self,
        toks: &[Token],
        k: &mut usize,
        out: &mut Vec<ClaimExpr>,
    ) -> Result<(), ParseError> {
        loop {
            let claim = self.parse_claim(toks, k)?;
            out.push(claim);
            if *k < toks.len() && toks[*k].kind == TokKind::Arrow {
                *k += 1;
                continue;
            }
            break;
        }
        Ok(())
    }

    fn parse_claim(&self, toks: &[Token], k: &mut usize) -> Result<ClaimExpr, ParseError> {
        let t = toks.get(*k).ok_or(ParseError {
            pos: Pos { line: 0, col: 0 },
            msg: "expected a claim".into(),
        })?;
        let pos = pos_of(t);
        if is_symbol(t, '(') {
            // conjunction: (A && B)
            *k += 1;
            let mut items = Vec::new();
            loop {
                let atom = self.parse_claim_atom(toks, k)?;
                items.push(atom);
                if *k < toks.len() && toks[*k].kind == TokKind::And {
                    *k += 1;
                    continue;
                }
                break;
            }
            let close = toks.get(*k).ok_or(ParseError {
                pos,
                msg: "expected `)`".into(),
            })?;
            if !is_symbol(close, ')') {
                return self.err(pos, "expected `)` to close conjunction");
            }
            *k += 1;
            return Ok(ClaimExpr::Conj { items, pos });
        }
        self.parse_claim_atom(toks, k)
    }

    fn parse_claim_atom(&self, toks: &[Token], k: &mut usize) -> Result<ClaimExpr, ParseError> {
        let t = toks.get(*k).ok_or(ParseError {
            pos: Pos { line: 0, col: 0 },
            msg: "expected a claim".into(),
        })?;
        let pos = pos_of(t);
        let name = match &t.kind {
            TokKind::Ident(id) => id.to_lowercase(),
            _ => return self.err(pos, "expected an identifier"),
        };
        *k += 1;

        // Ratio equality: `BD/DC = AB/AC`.
        if *k < toks.len() && is_symbol(&toks[*k], '/') {
            *k += 1;
            let den = self.parse_ratio_atom(toks, k)?;
            let lhs = RatioExpr::Quot {
                num: RatioAtom::Seg(name),
                den,
            };
            expect_symbol(toks, k, '=')?;
            let rhs = self.parse_ratio_expr(toks, k)?;
            return Ok(ClaimExpr::RatioEq { lhs, rhs, pos });
        }

        if *k < toks.len() && is_symbol(&toks[*k], '(') {
            if name == "distance" {
                // Distance(a, b) length expression starting an equality chain
                *k += 1;
                let a = expect_ident(toks, k)?.to_lowercase();
                expect_symbol(toks, k, ',')?;
                let b = expect_ident(toks, k)?.to_lowercase();
                expect_symbol(toks, k, ')')?;
                let mut items = vec![self.parse_sq_suffix(toks, k, LenExpr::Distance(a, b))?];
                self.parse_eq_chain_rest(toks, k, &mut items)?;
                return Ok(ClaimExpr::EqChain { items, pos });
            }
            // predicate call
            *k += 1;
            let mut args = Vec::new();
            while *k < toks.len() && !is_symbol(&toks[*k], ')') {
                let a = expect_ident(toks, k)?.to_lowercase();
                if a == "angle" && *k < toks.len() && is_symbol(&toks[*k], '(') {
                    // Angle(BAC) wrapper inside a predicate argument.
                    *k += 1;
                    let inner = expect_ident(toks, k)?.to_lowercase();
                    expect_symbol(toks, k, ')')?;
                    args.push(inner);
                } else {
                    args.push(a);
                }
                if *k < toks.len() && is_symbol(&toks[*k], ',') {
                    *k += 1;
                }
            }
            expect_symbol(toks, k, ')')?;
            // Triangle(ABC) = Triangle(MNP): explicit triangle equality.
            if name == "triangle"
                && args.len() == 1
                && *k < toks.len()
                && is_symbol(&toks[*k], '=')
                && *k + 2 < toks.len()
                && is_ident_word(&toks[*k + 1], "triangle")
                && is_symbol(&toks[*k + 2], '(')
            {
                let lhs = args[0].clone();
                *k += 1;
                *k += 1;
                expect_symbol(toks, k, '(')?;
                let rhs = expect_ident(toks, k)?.to_lowercase();
                expect_symbol(toks, k, ')')?;
                return Ok(ClaimExpr::TriCall { lhs, rhs, pos });
            }
            // Angle(ABC) = Angle(MNP): angle equality.
            if name == "angle"
                && args.len() == 1
                && *k < toks.len()
                && is_symbol(&toks[*k], '=')
                && *k + 2 < toks.len()
                && is_ident_word(&toks[*k + 1], "angle")
                && is_symbol(&toks[*k + 2], '(')
            {
                let lhs = args[0].clone();
                *k += 1;
                *k += 1;
                expect_symbol(toks, k, '(')?;
                let rhs = expect_ident(toks, k)?.to_lowercase();
                expect_symbol(toks, k, ')')?;
                return Ok(ClaimExpr::AngleEq { lhs, rhs, pos });
            }
            if *k < toks.len() && is_symbol(&toks[*k], '=') {
                *k += 1;
                let value = parse_value_at(toks, k)?;
                return Ok(ClaimExpr::PredEq {
                    name,
                    args,
                    value,
                    pos,
                });
            }
            return Ok(ClaimExpr::PredCall { name, args, pos });
        }

        // chained length equality: lhs = rhs = ...
        let mut items = vec![self.parse_sq_suffix(toks, k, LenExpr::Seg(name))?];
        self.parse_eq_chain_rest(toks, k, &mut items)?;
        // A two-term equality of three-character references denotes triangle
        // equality, e.g. `ABC = MNP`.
        if items.len() == 2 {
            if let (LenExpr::Seg(l), LenExpr::Seg(r)) = (&items[0], &items[1]) {
                if l.chars().count() == 3 && r.chars().count() == 3 {
                    return Ok(ClaimExpr::TriEq {
                        lhs: l.clone(),
                        rhs: r.clone(),
                        pos,
                    });
                }
            }
        }
        Ok(ClaimExpr::EqChain { items, pos })
    }

    /// Parse the `= x = y ...` tail of an equality chain, appending each
    /// length expression to `items`.
    fn parse_eq_chain_rest(
        &self,
        toks: &[Token],
        k: &mut usize,
        items: &mut Vec<LenExpr>,
    ) -> Result<(), ParseError> {
        expect_symbol(toks, k, '=')?;
        loop {
            items.push(self.parse_len_expr(toks, k)?);
            if *k < toks.len() && is_symbol(&toks[*k], '=') {
                *k += 1;
                continue;
            }
            break;
        }
        Ok(())
    }

    /// An optional `^2` suffix after a length expression, e.g. `BD^2`.
    fn parse_sq_suffix(
        &self,
        toks: &[Token],
        k: &mut usize,
        base: LenExpr,
    ) -> Result<LenExpr, ParseError> {
        if *k < toks.len() && is_symbol(&toks[*k], '^') {
            *k += 1;
            let t2 = toks.get(*k).ok_or(ParseError {
                pos: Pos { line: 0, col: 0 },
                msg: "expected `2` after `^`".into(),
            })?;
            match &t2.kind {
                TokKind::Number(2) => {
                    *k += 1;
                    Ok(LenExpr::Sq(Box::new(base)))
                }
                TokKind::Number(_) => self.err(pos_of(t2), "only ^2 (squared) is supported"),
                _ => self.err(pos_of(t2), "expected `2` after `^`"),
            }
        } else {
            Ok(base)
        }
    }

    /// Parse a length expression: a segment reference (`BD`), a numeric
    /// literal (`3`), or a `Distance(Point, Point)` call. A trailing `^2`
    /// wraps the expression, e.g. `BD^2` or `Distance(B,D)^2`.
    fn parse_len_expr(&self, toks: &[Token], k: &mut usize) -> Result<LenExpr, ParseError> {
        let t = toks.get(*k).ok_or(ParseError {
            pos: Pos { line: 0, col: 0 },
            msg: "expected a length expression".into(),
        })?;
        let pos = pos_of(t);
        let base = match &t.kind {
            TokKind::Number(n) => {
                *k += 1;
                LenExpr::Num(*n)
            }
            TokKind::Ident(_) => {
                let name = expect_ident(toks, k)?.to_lowercase();
                if *k < toks.len() && is_symbol(&toks[*k], '(') {
                    if name != "distance" {
                        return self.err(
                            pos,
                            "only `Distance` may be used as a length expression call",
                        );
                    }
                    *k += 1;
                    let a = expect_ident(toks, k)?.to_lowercase();
                    expect_symbol(toks, k, ',')?;
                    let b = expect_ident(toks, k)?.to_lowercase();
                    expect_symbol(toks, k, ')')?;
                    LenExpr::Distance(a, b)
                } else {
                    LenExpr::Seg(name)
                }
            }
            _ => return self.err(pos, "expected a length expression"),
        };
        self.parse_sq_suffix(toks, k, base)
    }

    /// Parse a ratio atom: a segment reference or an integer constant.
    fn parse_ratio_atom(&self, toks: &[Token], k: &mut usize) -> Result<RatioAtom, ParseError> {
        let t = toks.get(*k).ok_or(ParseError {
            pos: Pos { line: 0, col: 0 },
            msg: "expected a segment reference or number in a ratio".into(),
        })?;
        let pos = pos_of(t);
        match &t.kind {
            TokKind::Ident(id) => {
                *k += 1;
                Ok(RatioAtom::Seg(id.to_lowercase()))
            }
            TokKind::Number(n) => {
                *k += 1;
                Ok(RatioAtom::Int(*n))
            }
            _ => self.err(pos, "expected a segment reference or number in a ratio"),
        }
    }

    /// Parse a ratio expression: `atom (/ atom)?`, e.g. `AB`, `AB/AC`, `1/2`.
    fn parse_ratio_expr(&self, toks: &[Token], k: &mut usize) -> Result<RatioExpr, ParseError> {
        let num = self.parse_ratio_atom(toks, k)?;
        if *k < toks.len() && is_symbol(&toks[*k], '/') {
            *k += 1;
            let den = self.parse_ratio_atom(toks, k)?;
            Ok(RatioExpr::Quot { num, den })
        } else {
            match num {
                RatioAtom::Seg(s) => Ok(RatioExpr::Seg(s)),
                RatioAtom::Int(_) => self.err(
                    pos_of(&toks[(*k).saturating_sub(1)]),
                    "a bare number cannot stand alone as a ratio",
                ),
            }
        }
    }
}

// ---- helpers ----

fn pos_of(t: &Token) -> Pos {
    Pos {
        line: t.line,
        col: t.col,
    }
}

fn is_symbol(t: &Token, s: char) -> bool {
    matches!(&t.kind, TokKind::Symbol(c) if *c == s)
}

fn is_ident_word(t: &Token, w: &str) -> bool {
    matches!(&t.kind, TokKind::Ident(id) if id.eq_ignore_ascii_case(w))
}

/// True if the identifier starts a geometry construction (`Intersection(...)`,
/// `PerpendicularLine(...)`, `Midpoint(...)`) rather than a bare reference.
fn is_construction_word(id: &str) -> bool {
    matches!(
        id.to_lowercase().as_str(),
        "intersection"
            | "perpendicularline"
            | "prependicularline"
            | "parallelline"
            | "midpoint"
            | "anglebisector"
            | "altitude"
            | "circumcenter"
            | "incenter"
            | "orthocenter"
            | "centroid"
            | "pointon"
    )
}

fn expect_symbol(toks: &[Token], k: &mut usize, s: char) -> Result<(), ParseError> {
    let t = toks.get(*k).ok_or(ParseError {
        pos: Pos { line: 0, col: 0 },
        msg: format!("expected `{}`", s),
    })?;
    if is_symbol(t, s) {
        *k += 1;
        Ok(())
    } else {
        Err(ParseError {
            pos: pos_of(t),
            msg: format!("expected `{}`, found `{}`", s, token_str(t)),
        })
    }
}

/// Remove and verify the first token is a symbol.
fn expect_first_symbol(toks: &mut Vec<Token>, s: char) -> Result<(), ParseError> {
    if toks.is_empty() {
        return Err(ParseError {
            pos: Pos { line: 0, col: 0 },
            msg: format!("expected `{}`", s),
        });
    }
    let t = toks.remove(0);
    if is_symbol(&t, s) {
        Ok(())
    } else {
        Err(ParseError {
            pos: pos_of(&t),
            msg: format!("expected `{}`, found `{}`", s, token_str(&t)),
        })
    }
}

/// Remove and return the first token's identifier text.
fn expect_first_ident(toks: &mut Vec<Token>) -> Result<String, ParseError> {
    if toks.is_empty() {
        return Err(ParseError {
            pos: Pos { line: 0, col: 0 },
            msg: "expected an identifier".into(),
        });
    }
    let t = toks.remove(0);
    match &t.kind {
        TokKind::Ident(id) => Ok(id.clone()),
        _ => Err(ParseError {
            pos: pos_of(&t),
            msg: format!("expected an identifier, found `{}`", token_str(&t)),
        }),
    }
}

fn expect_ident<'a>(toks: &'a [Token], k: &mut usize) -> Result<&'a String, ParseError> {
    let t = toks.get(*k).ok_or(ParseError {
        pos: Pos { line: 0, col: 0 },
        msg: "expected an identifier".into(),
    })?;
    match &t.kind {
        TokKind::Ident(id) => {
            *k += 1;
            Ok(id)
        }
        _ => Err(ParseError {
            pos: pos_of(t),
            msg: format!("expected an identifier, found `{}`", token_str(t)),
        }),
    }
}

fn token_str(t: &Token) -> String {
    match &t.kind {
        TokKind::Ident(id) => id.clone(),
        TokKind::Number(n) => n.to_string(),
        TokKind::Symbol(c) => c.to_string(),
        TokKind::Arrow => "->".into(),
        TokKind::And => "&&".into(),
        TokKind::Or => "||".into(),
        TokKind::Newline => "<newline>".into(),
        TokKind::Eof => "<eof>".into(),
    }
}

fn parse_value_at(toks: &[Token], k: &mut usize) -> Result<Value, ParseError> {
    let t = toks.get(*k).ok_or(ParseError {
        pos: Pos { line: 0, col: 0 },
        msg: "expected a value".into(),
    })?;
    match &t.kind {
        TokKind::Ident(id) => {
            let low = id.to_lowercase();
            let v = match low.as_str() {
                "true" => Value::Bool(true),
                "false" => Value::Bool(false),
                "none" | "null" => Value::None_,
                "any" => Value::Any,
                _ => Value::Point(id.to_lowercase()),
            };
            *k += 1;
            Ok(v)
        }
        TokKind::Symbol('?') => {
            *k += 1;
            Ok(Value::Unknown)
        }
        _ => Err(ParseError {
            pos: pos_of(t),
            msg: format!("expected a value, found `{}`", token_str(t)),
        }),
    }
}

// ---- line classification ----

fn is_arrow_start(line: &Line) -> bool {
    matches!(line.toks.first().map(|t| &t.kind), Some(TokKind::Arrow))
}

fn is_proof_header(line: &Line) -> bool {
    line.toks.len() >= 3 && is_ident_word(&line.toks[0], "proof") && is_symbol(&line.toks[1], '[')
}

fn is_proof_property(line: &Line) -> bool {
    line.toks.len() >= 2
        && is_ident_word(&line.toks[0], "proofproperties")
        && is_symbol(&line.toks[1], '[')
}

fn is_goal_line(line: &Line) -> bool {
    line.toks.len() >= 2
        && matches!(&line.toks[0].kind, TokKind::Number(_))
        && is_symbol(&line.toks[1], '.')
}

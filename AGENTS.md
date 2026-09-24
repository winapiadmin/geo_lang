Here’s a practical map of the codebase, the public API, and where to look when extending or embedding it.

## 1. High-level architecture

The crate is both a library (`lib.rs`) and a binary (`main.rs`).

Pipeline:

```text
.geo source
  -> token::tokenize
  -> parser::parse
  -> ast::File
  -> checker::check / checker::build_facts_from_input
  -> prover::forward_saturate + prover::prove_seeded
  -> diag::render_diag / prover::render_chain
```

Modules:

| Module | Purpose |
|---|---|
| `token.rs` | Lexer for `.geo` |
| `parser.rs` | Recursive-descent parser |
| `ast.rs` | AST for input, goals, proofs, expressions |
| `claim.rs` | Normalized atomic claims and value types |
| `checker.rs` | Builds fact store, checks proofs/goals |
| `rules.rs` | Rule patterns, matching, instantiation |
| `rule_loader.rs` | Loads rule `.geo` files from `rules/` |
| `prover.rs` | Forward saturation + backward chaining prover |
| `symbolic.rs` | Numeric, ratio, coordinate, trig, Pythagoras solver |
| `diag.rs` | Diagnostics, spans, rendering, bypass |
| `main.rs` | CLI: `check`, `prove`, `help` |

---

## 2. CLI API

From `main.rs`:

```bash
geo_lang check <file.geo> [-e:Error1,Error2]
geo_lang prove <file.geo> [claim] [-disable:Rule1,Rule2] [-dump-facts=N]
geo_lang help
```

Useful flags:

- `-e:GoalNotProven,PremiseNotEstablished,...`  
  Downgrades listed error kinds to warnings/assumptions.

- `-disable:isosceles-altitude,median-midpoint,...`  
  Excludes rules from the prover. If a disabled rule has a `chain:` fallback, the prover may still reconstruct a proof using that chain.

- `-dump-facts=N`  
  Prints saturation facts per depth up to `N`.

Key CLI functions:

```rust
fn run_check(path: &str, bypass: &[String]) -> ExitCode
fn run_prove(
    path: &str,
    goal_arg: Option<&str>,
    disabled: &[String],
    dump_depth: Option<usize>,
) -> ExitCode
fn parse_single_claim(text: &str) -> Result<Vec<ast::ClaimExpr>, String>
fn bypass_names(args: &[String]) -> Vec<String>
fn disable_rules(args: &[String]) -> Vec<String>
```

---

## 3. Library API by module

### `token.rs`

```rust
pub fn tokenize(src: &str) -> Result<Vec<Token>, LexError>

pub enum TokKind {
    Ident(String),
    Number(f64),
    Symbol(char),
    Arrow,
    And,
    Or,
    Newline,
    Eof,
}

pub struct Token {
    pub kind: TokKind,
    pub line: usize,
    pub col: usize,
}

pub struct LexError {
    pub line: usize,
    pub col: usize,
    pub msg: String,
}
```

Notable behavior: merges `P[1]` into `P1`, except for `proof[...]`, `proofProperties[...]`, `inputProperties[...]`, `inp[...]`, `input[...]`.

---

### `parser.rs`

```rust
pub fn parse(source: &str, src_text: &str) -> Result<File, ParseError>

pub struct ParseError {
    pub pos: Pos,
    pub msg: String,
}
```

The parser is line-based but handles multi-line parenthesized calls and `->` continuation lines.

Useful parser entry points:

```rust
Parser::parse_file()
Parser::parse_goal()
Parser::parse_input_stmt()
Parser::parse_proof_header()
Parser::parse_step()
Parser::parse_claim()
Parser::parse_claim_atom()
Parser::parse_len_expr()
Parser::parse_ratio_expr()
```

---

### `ast.rs`

Core AST types:

```rust
pub struct File {
    pub source: String,
    pub lines: Vec<String>,
    pub input: Vec<InputStmt>,
    pub scoped_input: Vec<(u32, InputStmt)>,
    pub input_props: Vec<ProofProp>,
    pub goals: Vec<Goal>,
    pub props: Vec<ProofProp>,
    pub proofs: Vec<ProofBlock>,
}

pub struct Goal {
    pub index: u32,
    pub claim: Option<ClaimExpr>,
    pub calcs: Vec<CalcSpec>,
    pub pos: Pos,
}

pub enum ClaimExpr {
    EqChain { items: Vec<LenExpr>, pos: Pos },
    PredEq { name: String, args: Vec<String>, value: Value, pos: Pos },
    PredCall { name: String, args: Vec<String>, pos: Pos },
    Conj { items: Vec<ClaimExpr>, pos: Pos },
    Sum { lhs: Vec<SumTerm>, rhs: Vec<SumTerm>, pos: Pos },
    TriEq { lhs: String, rhs: String, pos: Pos },
    TriCall { lhs: String, rhs: String, pos: Pos },
    AngleEq { lhs: String, rhs: String, pos: Pos },
    RatioEq { lhs: RatioExpr, rhs: RatioExpr, pos: Pos },
}

pub enum InputStmt {
    Triangle { name, points, props, pos },
    Assign { name, geom, pos },
    Segment { a, b, pos },
    Line { a, b, pos },
    EqChain { items, pos },
    AngleEq { lhs, rhs, pos },
    PredFact { name, args, value, pos },
    RatioEq { lhs, rhs, pos },
}

pub enum Geom {
    Ref(String),
    Intersection(Vec<Geom>, Pos),
    PerpendicularLine { point, base, pos },
    ParallelLine { point, base, pos },
    Midpoint { a, b, pos },
    AngleBisector { vertex, base, pos },
    Altitude { vertex, base, pos },
    Center { kind, tri, pos },
    Line { a, b, pos },
    PointOn { seg, line_pts, pos },
    Circle { center, radius, pos },
}

pub enum LenExpr {
    Seg(String),
    Distance(String, String),
    Num(f64),
    Sq(Box<LenExpr>),
    Sqrt(Box<LenExpr>),
    Add(Box<LenExpr>, Box<LenExpr>),
    Sub(Box<LenExpr>, Box<LenExpr>),
    Mul(Box<LenExpr>, Box<LenExpr>),
    Div(Box<LenExpr>, Box<LenExpr>),
    Trig(String, String),
}

pub struct SumTerm {
    pub len: Option<LenExpr>,
    pub cos_angle: Option<String>,
    pub neg: bool,
}
```

Also:

```rust
pub enum Scope { Local, Global }
pub enum CalcSpec { Len(LenExpr), Angle(String) }
pub enum CenterKind { Circumcenter, Incenter, Orthocenter, Centroid }
pub enum RadiusSpec { Num(f64), Seg(String), ThroughPoint(String) }
```

---

### `claim.rs`

Normalized atomic claims used by the fact store and prover.

```rust
pub enum Claim {
    SegEq(String, String),
    RadiusEq(String, String),
    PredVal { name: String, args: Vec<String>, value: Value },
    On(String, String),
    OnSegment(String, String),
    OnLine(String, String),
    OnSameCircle(Vec<String>),
    IsoscelesAt(String, String),
    TriEq(String, String),
    AngleEq(String, String),
    RatioEq(RatioExpr, RatioExpr),
    LenEq(String, u32),
    SqEq(String, u32),
}

pub enum Value {
    Bool(bool),
    Point(String),
    None_,
    Any,
    Unknown,
}

pub enum RatioAtom {
    Seg(String),
    Int(u32),
}

pub enum RatioExpr {
    Seg(String),
    Quot { num: RatioAtom, den: RatioAtom },
}
```

Important constructors / normalizers:

```rust
Claim::seg_eq(lhs, rhs)
Claim::tri_eq(lhs, rhs)
Claim::angle_eq(lhs, rhs)
Claim::ratio_eq(lhs, rhs)
Claim::len_eq(seg, n)
Claim::sq_eq(seg, n)
Claim::pred(name, args, value)
Claim::on_circle(point, circle)
Claim::on_same_circle(points)

Claim::norm_ref(r)
Claim::norm_seg(r)
Claim::norm_tri(r)
Claim::norm_angle(r)
Claim::seg_key(a, b)
Claim::split_ref_names(seg)
```

Predicate display and normalization:

```rust
pub fn normalize_pred_name(name: &str) -> String
pub fn display_predicate(name: &str) -> String
```

---

### `checker.rs`

Builds and checks the fact store.

```rust
pub struct FactStore { ... }

impl FactStore {
    pub fn new() -> FactStore
    pub fn contains(&self, c: &Claim) -> bool
    pub fn add(&mut self, claim: Claim, origin: Origin) -> bool
    pub fn get(&self, c: &Claim) -> Option<&Fact>
    pub fn all(&self) -> Vec<Claim>
}

pub enum Origin {
    Input,
    Proof(u32, usize),
}
```

Main APIs:

```rust
pub fn check(file: &File) -> Vec<Diagnostic>
pub fn build_facts_from_input(file: &File) -> FactStore
pub fn apply_proofs(file: &File, facts: &mut FactStore) -> Vec<Diagnostic>
pub fn apply_input_statements(facts: &mut FactStore, stmts: &[&InputStmt])
pub fn claim_atoms(expr: &ClaimExpr) -> Vec<Claim>
pub fn derive_global_facts(facts: &mut FactStore)
pub fn derive_perpendicular_foot_midpoints(facts: &mut FactStore)
pub fn seg_eq_closure(facts: &mut FactStore)
pub fn circle_membership_closure(facts: &mut FactStore)
pub fn render_len_expr(e: &LenExpr) -> String
pub fn render_expr(expr: &ClaimExpr) -> String
pub fn atom_display_strings(expr: &ClaimExpr) -> Vec<String>
pub fn atom_display_len(e: &LenExpr) -> String
pub fn split_seg(seg: &str) -> Option<(String, String)>
```

Useful internal references:

- `process_input` handles `Triangle`, `Assign`, `Segment`, `Line`, `EqChain`, `PredFact`, `RatioEq`.
- `process_construction` handles `Intersection`, `PerpendicularLine`, `Midpoint`, `AngleBisector`, `Altitude`, `Center`, `PointOn`, `Circle`, etc.
- `process_proof` / `process_chain` / `establish` check proof steps.
- `check_goals` verifies `prove:` goals.

---

### `rules.rs`

Rule patterns and matching engine.

```rust
pub enum PExpr {
    PtVar(String),
    Seg2(String, String),
    Tri3(String, String, String),
    PtRef(String),
    SegRef(String),
    TriRef(String),
    AnyRef(String),
}

pub enum PRatioAtom {
    Expr(PExpr),
    Int(u32),
}

pub enum PRatioExpr {
    Seg(PExpr),
    Quot { num: PRatioAtom, den: PRatioAtom },
    Int(u32),
}

pub enum PClaim {
    SegEq(PExpr, PExpr),
    TriEq(PExpr, PExpr),
    AngleEq(PExpr, PExpr),
    RatioEq(PRatioExpr, PRatioExpr),
    PredVal(String, Vec<PExpr>, Value),
    PredAt(String, Vec<PExpr>, PExpr),
    On(PExpr, PExpr),
    IsoscelesAt(PExpr, PExpr),
    OnSameCircle(Vec<PExpr>),
}

pub struct Rule {
    pub id: &'static str,
    pub antecedents: Vec<PClaim>,
    pub requires: Vec<PClaim>,
    pub consequent: PClaim,
    pub chain: Option<&'static str>,
}

pub type Bindings = HashMap<String, String>;
```

Matching / instantiation:

```rust
pub fn match_expr(refval: &str, e: &PExpr, bind: &Bindings) -> Vec<Bindings>
pub fn match_pat(claim: &Claim, pat: &PClaim, bind: &Bindings) -> Vec<Bindings>
pub fn instantiate(pat: &PClaim, bind: &Bindings) -> Claim
pub fn render_expr(e: &PExpr, bind: &Bindings) -> String
pub fn apply_rule(rule: &Rule, facts: &[Claim], extra: &[Claim], goal: &Claim) -> Vec<Bindings>
pub fn find_hint(facts: &[Claim], extra: &[Claim], goal: &Claim, rules: &[Rule]) -> Option<Claim>
pub fn derive_all(chain: &[Claim], hints: &[&str]) -> Vec<Claim>
pub fn rule_base() -> Vec<Rule>
```

`rule_base()` loads all rule files from `rules/` via `rule_loader`.

---

### `rule_loader.rs`

Loads `.geo` rule files.

```rust
pub fn load_rules_from_dir(dir: &Path) -> Result<Vec<Rule>, String>
pub fn parse_fallback_chain(chain: &str) -> Result<Vec<FallbackStep>, String>
pub(crate) fn parse_claim(line: &str, section: &str, path: &Path) -> Result<PClaim, String>
```

Rule file format:

```text
rule: rule-id
antecedents:
  - PredicateName(arg1, arg2)
  - ...
requires:
  - PredicateName(arg1, ...)
consequent:
  - PredicateName(arg1, ...)
chain: step1 [rule1] -> step2 [rule2] -> ...
```

Validation:

```rust
fn validate_chain_metadata(rules: &[Rule]) -> Result<(), String>
```

Checks that every `[rule-id]` in a fallback chain resolves and does not self-reference, and that the chain ends with the declared consequent.

---

### `prover.rs`

Forward saturation + backward chaining.

```rust
pub const MAX_DEPTH: usize = 16;

pub struct Proof {
    pub claim: Claim,
    pub antecedents: Vec<Proof>,
    pub rule: Option<&'static str>,
}
```

Main APIs:

```rust
pub fn forward_saturate(facts: &FactStore, rules: &[Rule]) -> FactStore
pub fn forward_saturate_d(
    facts: &FactStore,
    rules: &[Rule],
    dump_depth: Option<usize>,
) -> FactStore
pub fn saturate_toward(
    facts: &FactStore,
    rules: &[Rule],
    goal: Option<&Claim>,
    dump_depth: Option<usize>,
) -> FactStore

pub fn prove(
    goal: &Claim,
    facts: &FactStore,
    rules: &[Rule],
    depth: usize,
) -> Option<Proof>

pub fn prove_seeded(
    goal: &Claim,
    facts: &FactStore,
    saturated: &FactStore,
    rules: &[Rule],
    disabled: Option<&HashSet<&str>>,
) -> Option<Proof>

pub fn prove_similarity_aa(goal: &Claim, facts: &FactStore) -> Option<Proof>
```

Rendering:

```rust
pub fn to_chain(p: &Proof) -> Vec<(String, bool)>
pub fn render_chain(p: &Proof, final_display: Option<&str>) -> String
pub fn render_checkable_chain(p: &Proof, final_display: Option<&str>) -> String
pub fn render_compound_proof(p: &Proof, final_display: &str) -> String
pub fn render_tree(p: &Proof, indent: usize, final_display: Option<&str>) -> String
```

Important notes:

- `forward_saturate*` skips some explosive rules: `invthales`, `subset-parallel*`, `midpoint-ratio*`, `similarity-proportional*`, `parallel-corresponding*`, `ratio-double`.
- `prove_seeded` runs numeric/coordinate proofs first, then rule-based backward chaining, then numeric fallback.
- `prove_similarity_aa` tries AA similarity via `AngleEq`, right angles, and shared rays.

---

### `symbolic.rs`

Numeric / ratio / coordinate / trig solver.

```rust
pub type EXRat = dashu::rational::RBig;

pub struct NumericEnv {
    pub lens: HashMap<String, u32>,
    pub sq: HashMap<String, u32>,
    pub conflicts: Vec<LenConflict>,
}

pub struct LenConflict {
    pub seg: String,
    pub old: u32,
    pub new: u32,
}
```

Main APIs:

```rust
pub fn compute(facts: &FactStore) -> NumericEnv
pub fn solve_len(seg: &str, facts: &FactStore) -> Option<u32>
pub fn eval_len_expr(e: &LenExpr, facts: &FactStore) -> Option<f64>
pub fn eval_len_expr_ratio(e: &LenExpr, facts: &FactStore) -> Option<EXRat>
pub fn resolve_seg_ratio(seg: &str, facts: &FactStore) -> Option<EXRat>
pub fn ratio_derivation_proof(seg: &str, facts: &FactStore) -> Option<Proof>
pub fn ratio_solves(goal: &Claim, facts: &FactStore) -> bool
pub fn numeric_solves(goal: &Claim, facts: &FactStore) -> bool
pub fn numeric_proof(goal: &Claim, facts: &FactStore) -> Option<Proof>
pub fn explain_len(env: &NumericEnv, seg: &str, n: u32) -> Proof
pub fn explain_sq(env: &NumericEnv, seg: &str, v: u32) -> Proof
```

Trig / angle / identity APIs:

```rust
pub fn cos_of_vertex(tri: &str, vertex: char, facts: &FactStore) -> Option<f64>
pub fn angle_degrees(tri: &str, vertex: char, facts: &FactStore) -> Option<f64>
pub fn angle_degrees_any(vertex: &str, facts: &FactStore) -> Option<(String, f64)>
pub fn angle_proof(vertex: &str, facts: &FactStore) -> Option<Proof>

pub fn sum_solves(
    lhs: &[SumTerm],
    rhs: &[SumTerm],
    facts: &FactStore,
) -> bool

pub fn sum_solves_trig(
    lhs: &[SumTerm],
    rhs: &[SumTerm],
    facts: &FactStore,
) -> bool

pub fn sum_premises(
    lhs: &[SumTerm],
    rhs: &[SumTerm],
    facts: &FactStore,
) -> Vec<String>

pub fn sum_trig_chain(...) -> Option<String>
pub fn sum_trig_steps(...) -> Vec<String>

pub fn eq_chain_solves_trig(items: &[LenExpr], facts: &FactStore) -> bool
pub fn eq_chain_trig_steps(items: &[LenExpr], tri: &str, apex: char) -> Vec<String>

pub fn law_of_cosines_solves(items: &[LenExpr], facts: &FactStore) -> bool
pub fn law_of_cosines_derive(items: &[LenExpr], facts: &FactStore) -> Option<Vec<String>>
pub fn law_of_cosines_proof(items: &[LenExpr], facts: &FactStore) -> Option<Proof>

pub fn rectangle_diagonal_derive(items: &[LenExpr], facts: &FactStore) -> Option<Vec<String>>
pub fn rectangle_diagonal_proof(items: &[LenExpr], facts: &FactStore) -> Option<Proof>
```

Coordinate helpers:

```rust
pub struct Rational { ... }
pub struct LineCoords { ... }

pub fn derive_ratios_from_midpoints(facts: &FactStore, coords: &mut LineCoords)
pub fn eval_ratio(e: &RatioExpr, coords: &LineCoords) -> Option<(i64, i64)>
pub fn eval_atom(a: &RatioAtom, coords: &LineCoords) -> Option<(i64, i64)>
```

---

### `diag.rs`

Diagnostics and bypass handling.

```rust
pub enum Severity { Error, Warning }

pub struct Span {
    pub line: usize,
    pub col: usize,
    pub len: usize,
}

pub struct Diagnostic {
    pub severity: Severity,
    pub span: Span,
    pub message: String,
    pub kind: &'static str,
    pub hint: Option<String>,
    pub note: Option<String>,
}

impl Diagnostic {
    pub fn error(span: Span, msg: impl Into<String>) -> Diagnostic
    pub fn warning(span: Span, msg: impl Into<String>) -> Diagnostic
    pub fn with_kind(self, kind: &'static str) -> Diagnostic
    pub fn with_hint(self, hint: impl Into<String>) -> Diagnostic
    pub fn with_note(self, note: impl Into<String>) -> Diagnostic
    pub fn is_error(&self) -> bool
}

pub fn bypass_errors(diags: Vec<Diagnostic>, names: &[String]) -> Vec<Diagnostic>
pub fn render_diag(source: &str, lines: &[String], diag: &Diagnostic) -> String
```

Diagnostic kinds used by `-e:` include:

- `goal-not-proven`
- `premise-not-established`
- `wrong-result`

Bypass normalization strips separators and lower-cases, so `GoalNotProven`, `goal-not-proven`, and `goalnotproven` all match.

---

## 4. Common embedding example

```rust
use geo_lang::{ast, checker, diag, parser, prover, rules, symbolic};

let source = "example.geo";
let src_text = std::fs::read_to_string(source)?;
let file = parser::parse(source, &src_text)?;

// Check proofs and goals
let diagnostics = checker::check(&file);
for d in &diagnostics {
    println!("{}", diag::render_diag(&file.source, &file.lines, d));
}

// Prove a goal
let facts = checker::build_facts_from_input(&file);
let rule_base = rules::rule_base();
let saturated = prover::forward_saturate(&facts, &rule_base);

let goal = /* a Claim */;
if let Some(proof) = prover::prove_seeded(
    &goal,
    &facts,
    &saturated,
    &rule_base,
    None,
) {
    println!("{}", prover::render_chain(&proof, None));
    println!("{}", prover::render_tree(&proof, 0, None));
}
```

---

## 5. Where to look when extending

| Task | Files |
|---|---|
| Add a new construction | `ast.rs`, `parser.rs::parse_geom`, `checker.rs::process_construction` |
| Add a new predicate | `claim.rs::normalize_pred_name/display_predicate`, `checker.rs::KNOWN_PREDS`, `rule_loader.rs::parse_predicate` |
| Add a new rule | Create `.geo` file in `rules/`, loaded by `rule_loader.rs` |
| Add a new numeric/trig identity | `symbolic.rs` |
| Change proof rendering | `prover.rs::render_chain`, `render_tree`, `render_checkable_chain` |
| Change diagnostics | `diag.rs` |
| Change scoped proof/input behavior | `checker.rs::apply_proofs`, `check_goals`, `parser.rs` section handling |
| Change saturation behavior | `prover.rs::saturate_toward`, `join_rule`, rule filters |

Most useful entry points for debugging:

- `checker::check`
- `checker::build_facts_from_input`
- `prover::forward_saturate_d` with `-dump-facts`
- `symbolic::compute`
- `prover::prove_seeded`
- `diag::render_diag`
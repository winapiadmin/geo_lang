# geo_lang fixes

Drop these files into your repo at the same paths, overwriting the existing
ones (they're each a full, complete replacement — not a diff/patch):

- src/prover.rs
- src/symbolic.rs
- src/rules.rs
- src/main.rs
- src/bin/debug_prob12.rs
- tests/integration.rs

After copying, delete Cargo.lock if it fails to parse ("lock file version 4
requires...") and let `cargo build` regenerate it.

## What changed and why

### 1. `src/prover.rs` — the bulk of the work

- **`ratio_conflicts` + lenient check for `metric-relations` /
  `angle-bisector-theorem`**: forward saturation was rejecting every
  `RatioEq` fact these two rules produced whenever the problem had no
  numeric side lengths to verify against (i.e. almost any pure symbolic
  ratio proof), which is what originally caused `prob12.geo`'s proof[3]
  (`KA*AB=KH*CB`) to fail outright.

- **`is_degenerate`**: broadened to catch a degenerate atom *anywhere*
  inside a `RatioEq` (e.g. the `AA` in `AA/BC = AC/BH`), not just the
  narrow "both sides are literally X/X" case, and to catch a 3-letter
  triangle ref with a repeated point (e.g. `IsSimilar(AAC,BCH)`). This was
  causing combinatorial blow-up in forward saturation once the above fix
  let more `RatioEq` facts through.

- **`join_rule`'s `requires:` handling**: a `requires:` clause referencing a
  variable that doesn't appear in any `antecedents:` (e.g. `Q` in
  `medial-segment-midpoint`'s `requires: IsMedian(Q, Seg2(B,C))`) was
  silently instantiated with an empty-string placeholder and could never
  match — the rule was permanently dead. Now falls back to a store join
  when a `requires` clause still has an unbound variable.

- **`match_pat`'s `PredVal` case** (in `rules.rs`, called from here): added
  permutation-aware matching for `iscollinear`, since its claim
  representation sorts its 3 args alphabetically on construction, which
  broke positional pattern matching in the disabled-rule fallback-chain
  logic (`IsCollinear(Q,J,H)` is stored as `(H,J,Q)`).

- **The `structural`/`symbolic` antecedent partition**: `RatioEq`
  antecedents with a variable that only appears in *another* `RatioEq`
  antecedent of the same rule (a "bridge" variable, e.g. `E,F,G,H` in
  `ratio-transitivity`) could never get bound and the rule could never be
  proven backward. Added a post-structural-join "rescue pass" that
  specifically handles this case, *without* reclassifying every
  under-bound `RatioEq` up front (an earlier, blunter version of this fix
  broke `invthales`/parallel-from-ratio cases where the missing variable
  *is* resolvable by an ordinary structural antecedent in the same rule,
  and needs the numeric-check path, not a literal fact-store lookup).

- **`claims_equiv`** (the cycle guard): now also treats `RatioEq(l,r)` and
  `RatioEq(r,l)` as the same claim, so backward search doesn't miss a goal
  reappearing in swapped form.

- **Reciprocal-goal fallback**: before giving up and rendering an
  unexplained `[fact]` leaf, a `RatioEq` goal now also tries its
  reciprocal (`a/b=c/d` ⟺ `b/a=d/c`) via a new synthetic
  `"ratio-reciprocal"` rule label, since forward-saturated ratio chains
  can land on either orientation.

- **The disabled-rule fallback-chain matcher**: removed the temporary
  `eprintln!` debug instrumentation used to diagnose the
  `prob3_nine_point_without_cheat_rule` failure.

- **Recursive-before-leaf**: when a symbolic antecedent is present in the
  *saturated* (forward-derived) store but isn't a genuine base fact, the
  code now tries to recursively explain it via `prove_rec` before falling
  back to a bare, unexplained `[fact]` leaf.

### 2. `src/rules.rs`

- Permutation-aware `iscollinear` matching in `match_pat` (see above).

### 3. `src/symbolic.rs`

- `eq_chain_solves_trig` now returns the winning `(triangle, apex)` pair
  instead of a bare `bool`, so the caller renders proof steps for the same
  right-triangle candidate that was actually verified (previously it could
  verify against one triangle, e.g. `AHB`, but render against the first
  `RightAt` fact in the store, e.g. `ABC`, producing nonsense).
- `eq_chain_trig_steps`: fixed the `SIN`/`COS`/`TAN` display bug (was
  literally printing the uppercased function name with no angle argument,
  e.g. `AB*SIN=...`) and a real (not just cosmetic) leg-selection bug — all
  three functions used the same `leg/hyp` formula, and even `sin` picked
  the *adjacent* leg where it needed the *opposite* one. Now renders
  `sin`/`cos`/`tan` with the mathematically correct opposite/adjacent/hyp
  legs and a properly-cased angle argument, e.g. `AB*sin(ACB)=AB*HB/AB`.
- Added `ratio_conflicts` (see prover.rs above).

### 4. `src/main.rs`

- Updated the one call site of `eq_chain_solves_trig` for its new
  `Option<(String, char)>` return type, using the returned pair for
  rendering instead of independently picking the first `RightAt` fact in
  the store.

### 5. `src/bin/debug_prob12.rs`

- Fixed a pre-existing syntax error (missing closing brace) that was
  present in the file as shipped, unrelated to any of the above.

### 6. `tests/integration.rs`

- `prob3_nine_point_without_cheat_rule`: switched from the goal-less
  `forward_saturate` (full closure to depth 64 — 98s and, after the
  correctness fixes above made the closure bigger, an OOM) to goal-directed
  `saturate_toward`, which early-exits once the target is derivable
  (98s → ~0.1s).
- `nothing_skips_rest_of_proof`: the general auto-prover fallback (a
  safety net separate from `Step::Nothing`, always tried regardless of
  whether the written proof was skipped) started legitimately proving the
  test's goal once the bugs above were fixed, since it was a true,
  generally-provable fact (isosceles altitude = median). Changed the test's
  triangle to a non-isosceles one so the goal is genuinely unprovable by
  any means, which is what the test is actually supposed to be checking.

## Known remaining issue (not fixed)

Proof[3] for `prob12.geo` (`KA*AB=KH*CB`) now cites a real rule
(`ratio-transitivity`) instead of an unexplained `[fact]`, but the
top-level rendered tree in the normal CLI path sometimes doesn't show the
full nested antecedent chain (angle-bisector-theorem + similarity), even
though an isolated test of the same underlying `prove_seeded` call does
show it fully nested. This looks like the specific `Proof` value picked up
by that code path in `main.rs` differs from what a fresh call finds
(possibly due to state/goal-order dependence across earlier goals in the
same `.geo` file) — flagged for further investigation, not resolved here.

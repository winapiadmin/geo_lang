//! Backward-chaining prover.
//!
//! Given a goal claim, the prover searches the rule base for a chain of rule
//! applications whose premises are already established facts (leaves). The
//! resulting proof can be rendered both as a tree and as a single `->` chain
//! matching the language's proof-step syntax.

use crate::checker::{FactStore, Origin};
use crate::claim::Claim;
use crate::rules::{instantiate, match_pat, Bindings, Rule, PClaim};
use std::collections::HashMap;

pub const MAX_DEPTH: usize = 16;

/// How many new facts the forward pass may derive per goal.
const MAX_SATURATION: usize = 200_000;

/// Safety cap on intermediate rule bindings per saturation pass.
const MAX_BINDINGS: usize = 4_000_000;

/// Check if two claims are equivalent for cycle-detection purposes.
/// For symmetric predicates (IsParallel, IsPerpendicular), the args are
/// compared in sorted order so that `A⊥B` ≡ `B⊥A`.
fn claims_equiv(a: &Claim, b: &Claim) -> bool {
    match (a, b) {
        (
            Claim::PredVal { name: n1, args: a1, value: v1 },
            Claim::PredVal { name: n2, args: a2, value: v2 },
        ) if n1 == n2 && v1 == v2 && a1.len() == 2 && a2.len() == 2 => {
            let symmetric = matches!(
                n1.as_str(),
                "isperpendicular" | "isparallel" | "isperpendicularbisector"
            );
            if symmetric {
                let mut p1 = [a1[0].clone(), a1[1].clone()];
                let mut p2 = [a2[0].clone(), a2[1].clone()];
                p1.sort();
                p2.sort();
                p1 == p2
            } else {
                a1 == a2
            }
        }
        _ => a == b,
    }
}

/// True for claims that are degenerate by construction, e.g. a "segment"
/// whose endpoints coincide (`II`) or a predicate relating a segment to itself
/// (`IsParallel(AB,AB)`) — such bindings carry no geometric content and only
/// bloat the closure.
fn is_degenerate(c: &Claim) -> bool {
    fn deg_seg(s: &str) -> bool {
        let n = Claim::norm_seg(s);
        n.len() == 2 && n.as_bytes()[0] == n.as_bytes()[1]
    }
    match c {
        Claim::SegEq(a, b) => deg_seg(a) || deg_seg(b),
        Claim::PredVal { name, args, .. } => {
            let seg_pred = matches!(
                name.as_str(),
                "isparallel" | "isperpendicular" | "ismedian" | "isaltitude"
            );
            if seg_pred && args.len() == 2 {
                if deg_seg(&args[0]) || deg_seg(&args[1]) {
                    return true;
                }
                // Self-referential: e.g. IsParallel(AB,AB), IsParallel(AB,BA),
                // IsPerpendicular(AB,AB), etc.
                let n0 = Claim::norm_seg(&args[0]);
                let n1 = Claim::norm_seg(&args[1]);
                if n0 == n1 {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

/// Derive the closure of `facts` under `rules` (sound forward chaining), used
/// to seed the backward prover with facts that follow directly from the input.
pub fn forward_saturate(facts: &FactStore, rules: &[Rule]) -> FactStore {
    saturate_toward(facts, rules, None)
}

/// Like [`forward_saturate`] but stops as soon as `goal` becomes derivable.
///
/// Semi-naive evaluation: after the first pass, a rule application only
/// contributes when at least one of its matches involves a fact derived in
/// the previous pass, which keeps later passes proportional to the delta.
fn saturate_toward(facts: &FactStore, rules: &[Rule], goal: Option<&Claim>) -> FactStore {
    let mut store = FactStore::new();
    let mut delta: Vec<Claim> = Vec::new();
    for f in facts.all() {
        if store.add(f.clone(), Origin::Input) {
            delta.push(f);
        }
    }
    if let Some(g) = goal {
        if store.contains(g) {
            return store;
        }
    }
    let base = facts.all().len();

    // Join `rule` against the store; each binding remembers how many of its
    // antecedent matches involved a *novel* (delta) fact. Facts are bucketed
    // by shape so each antecedent only scans plausible candidates.
    fn claim_shape(c: &Claim) -> String {
        match c {
            Claim::SegEq(_, _) => "segeq".into(),
            Claim::PredVal { name, args, value: _ } => {
                format!("p|{name}|{}", args.len())
            }
            Claim::On(_, _) => "on".into(),
            Claim::OnSegment(_, _) => "onseg".into(),
            Claim::OnLine(_, _) => "online".into(),
            Claim::IsoscelesAt(_, _) => "iso".into(),
            Claim::TriEq(_, _) => "trieq".into(),
            Claim::AngleEq(_, _) => "angle".into(),
            Claim::RatioEq(_, _) => "ratio".into(),
            Claim::LenEq(_, _) => "len".into(),
            Claim::SqEq(_, _) => "sq".into(),
            Claim::OnSameCircle(v) => format!("circ|{}", v.len()),
            Claim::RadiusEq(_, _) => "radius".into(),
        }
    }

    type Bucketed<'a> = std::collections::HashMap<String, Vec<&'a Claim>>;

    fn build_index(full: &[Claim]) -> Bucketed<'_> {
        let mut idx: Bucketed = std::collections::HashMap::new();
        for f in full {
            idx.entry(claim_shape(f)).or_default().push(f);
        }
        idx
    }

    fn join_rule(
        rule: &Rule,
        idx: &Bucketed,
        delta: &std::collections::HashSet<Claim>,
        first_pass: bool,
    ) -> Vec<Claim> {
        let mut cur: Vec<(Bindings, usize, std::collections::HashSet<String>)> =
            vec![(Bindings::new(), 0, std::collections::HashSet::new())];
        for ant in &rule.antecedents {
            // Candidate facts: those whose shape can possibly match.
            let mut cands: Vec<&Claim> = Vec::new();
            collect_shape_candidates(ant, idx, &mut cands);
            let mut next = Vec::new();
            'outer: for (bind, dcount, used) in &cur {
                for f in &cands {
                    if used.contains(&f.to_string()) {
                        continue;
                    }
                    let novel = delta.contains(*f);
                    for nb in match_pat(f, ant, bind) {
                        let mut new_used = used.clone();
                        new_used.insert(f.to_string());
                        next.push((nb, dcount + usize::from(novel), new_used));
                        if next.len() > MAX_BINDINGS {
                            break 'outer;
                        }
                    }
                }
            }
            cur = next;
            if cur.is_empty() {
                break;
            }
        }
        // Semi-naive filter: keep only bindings that used >=1 novel fact
        // (on the first pass every fact counts as novel).
        let mut out = Vec::new();
        for (bind, dcount, _used) in cur {
            if !first_pass && dcount == 0 {
                continue;
            }
            let mut ok = true;
            for req in &rule.requires {
                let inst = instantiate(req, &bind);
                if inst.has_unbound() || !full_contains(idx, &inst) {
                    ok = false;
                    break;
                }
            }
            if !ok {
                continue;
            }
            let c = instantiate(&rule.consequent, &bind);
            if !c.has_unbound() && !is_degenerate(&c) {
                out.push(c);
            }
        }
        out
    }

    // Gather all facts whose shape could possibly match `ant` (conservative:
    // includes every bucket when the antecedent is shape-polymorphic).
    fn collect_shape_candidates<'a>(
        ant: &PClaim,
        idx: &Bucketed<'a>,
        out: &mut Vec<&'a Claim>,
    ) {
        use crate::rules::PClaim as P;
        let keys: Vec<String> = match ant {
            P::SegEq(_, _) => vec!["segeq".into()],
            P::PredVal(n, a, _) => vec![format!("p|{}|{}", n, a.len())],
            P::PredAt(n, a, _) => vec![format!("p|{}|{}", n, a.len() + 0)],
            P::On(_, _) => vec!["on".into()],
            P::IsoscelesAt(_, _) => vec!["iso".into()],
            P::TriEq(_, _) => vec!["trieq".into()],
            P::AngleEq(_, _) => vec!["angle".into()],
            P::RatioEq(_, _) => vec!["ratio".into()],
            P::OnSameCircle(v) => vec![format!("circ|{}", v.len())],
        };
        for k in keys {
            if let Some(b) = idx.get(&k) {
                out.extend(b.iter().copied());
            }
        }
    }

    fn full_contains(idx: &Bucketed, c: &Claim) -> bool {
        idx.get(&claim_shape(c))
            .map(|b| b.iter().any(|f| *f == c))
            .unwrap_or(false)
    }

    let mut passes = 0usize;
    let mut closure_runs = 0usize;
    while !delta.is_empty() && passes < 64 {
        let current = store.all();
        let index = build_index(&current);
        let delta_set: std::collections::HashSet<Claim> = delta.iter().cloned().collect();
        let mut new_delta: Vec<Claim> = Vec::new();
        for rule in rules {
            if rule.id.contains("invthales")
                || rule.id.starts_with("subset-parallel")
                || rule.id.starts_with("midpoint-ratio")
                || rule.id.starts_with("similarity-proportional")
                || rule.id.starts_with("parallel-corresponding")
                || rule.id.starts_with("ratio-double")
            {
                continue;
            }
            for c in join_rule(rule, &index, &delta_set, passes == 0) {
                if !store.contains(&c) {
                    store.add(c.clone(), Origin::Proof(0, 0));
                    new_delta.push(c.clone());
                    if let Some(g) = goal {
                        if g == &c {
                            return store;
                        }
                    }
                }
            }
        }
        delta = new_delta;
        passes += 1;
        if store.all().len() > base + MAX_SATURATION {
            break;
        }
    }
    // Second pass: apply rules that were skipped in the main loop to produce
    // derived facts (AngleEq, RatioEq, On from IsMedian) needed by backward
    // chaining. These rules are kept separate because they can cause
    // combinatorial explosion if applied during the main saturation.
    {
        let skipped_ids: &[&str] = &[
            "subset-parallel", "subset-parallel-right",
            "midpoint-ratio", "midpoint-ratio-right",
            "similarity-proportional-sides", "similarity-proportional-sides-2", "similarity-proportional-sides-3",
            "parallel-corresponding-angles", "parallel-corresponding-angles-2",
            "ratio-double",
            "median-implies-on",
            "aa-similarity",
            "similarity-symmetry",
            "collinearity-via-midpoint",
            "segment-bisector-median",
            "ratio-same-denom-segeq",
            "ratio-same-denom-segeq-inv",
        ];
        let skipped_rules: Vec<&Rule> = rules.iter()
            .filter(|r| skipped_ids.iter().any(|id| r.id == *id))
            .collect();
        let mut delta: Vec<Claim> = store.all();
        let mut p2 = 0usize;
        while !delta.is_empty() && p2 < 4 {
            let current = store.all();
            let index = build_index(&current);
            let delta_set: std::collections::HashSet<Claim> = delta.iter().cloned().collect();
            let mut new_delta: Vec<Claim> = Vec::new();
            for rule in &skipped_rules {
                for c in join_rule(rule, &index, &delta_set, p2 == 0) {
                    if !store.contains(&c) {
                        store.add(c.clone(), Origin::Proof(0, 0));
                        new_delta.push(c.clone());
                    }
                }
            }
            delta = new_delta;
            p2 += 1;
        }
    }
    // Checker-side closures may unlock new length equalities once derived
    // facts (e.g. circumcenter equidistance) exist; stabilize.
    while closure_runs < 4 {
        closure_runs += 1;
        let before = store.all().len();
        crate::checker::seg_eq_closure(&mut store);
        crate::checker::circle_membership_closure(&mut store);
        if store.all().len() == before {
            break;
        }
        let mut p2 = 0usize;
        delta = store.all();
        while !delta.is_empty() && p2 < 8 {
            let current = store.all();
            let index = build_index(&current);
            let delta_set: std::collections::HashSet<Claim> = delta.iter().cloned().collect();
            let mut new_delta: Vec<Claim> = Vec::new();
            for rule in rules {
                if rule.id.contains("invthales")
                    || rule.id.starts_with("subset-parallel")
                    || rule.id.starts_with("midpoint-ratio")
                    || rule.id.starts_with("similarity-proportional")
                    || rule.id.starts_with("parallel-corresponding")
                    || rule.id.starts_with("ratio-double")
                {
                    continue;
                }
                for c in join_rule(rule, &index, &delta_set, false) {
                    if !store.contains(&c) {
                        store.add(c.clone(), Origin::Proof(0, 0));
                        new_delta.push(c.clone());
                        if let Some(g) = goal {
                            if g == &c {
                                return store;
                            }
                        }
                    }
                }
            }
            delta = new_delta;
p2 += 1;
        }
    }
    store
}

#[derive(Debug, Clone)]
pub struct Proof {
    pub claim: Claim,
    /// Empty for facts that are already established.
    pub antecedents: Vec<Proof>,
    /// The rule that produced this claim, if any.
    pub rule: Option<&'static str>,
}

impl Proof {
    fn leaf(claim: Claim) -> Proof {
        Proof { claim, antecedents: vec![], rule: None }
    }
}

/// Try to prove `goal` from `facts` using `rules`.
///
/// Strategy: forward-saturate the fact store (deriving every consequence the
/// rule base can reach), then run a join-based backward pass in which every
/// antecedent must match an established fact. This keeps the search complete
/// over the fact space and free of partially-bound subgoals.
pub fn prove(
    goal: &Claim,
    facts: &FactStore,
    rules: &[Rule],
    depth: usize,
) -> Option<Proof> {
    let _ = depth;

    // Numeric derivations (lengths, ratios, coordinates, Pythagoras) come first.
    if let Some(p) = crate::symbolic::numeric_proof(goal, facts) {
        return Some(p);
    }


    let saturated = saturate_toward(facts, rules, Some(goal));
    prove_inner(goal, &saturated, rules, facts)
}

/// Prove `goal` against a pre-computed saturated store (see
/// [`forward_saturate`]). Lets callers amortize one saturation across many
/// goals; falls back to the base facts for numeric derivations.
pub fn prove_seeded(
    goal: &Claim,
    facts: &FactStore,
    saturated: &FactStore,
    rules: &[Rule],
) -> Option<Proof> {
    // Numeric / coordinate derivations run against the base facts.
    if let Some(p) = crate::symbolic::numeric_proof(goal, facts) {
        return Some(p);
    }
    prove_inner(goal, saturated, rules, facts)
}

/// Join-based backward chaining: structural antecedents must match facts;
/// *symbolic* antecedents (`RatioEq`/`LenEq`/`SqEq`/`SegEq`) may additionally
/// be discharged by the numeric/coordinate solver over the base facts.
/// Bindings are extended by full matches only, so no partially-instantiated
/// claim is ever constructed.
/// Depth budget for reconstructing nested derivation trees.
const PROOF_DEPTH: usize = 12;

fn prove_inner(
    goal: &Claim,
    saturated: &FactStore,
    rules: &[Rule],
    base: &FactStore,
) -> Option<Proof> {
    prove_rec(goal, saturated, rules, base, PROOF_DEPTH, &[])
}

fn prove_rec(
    goal: &Claim,
    saturated: &FactStore,
    rules: &[Rule],
    base: &FactStore,
    depth: usize,
    ancestors: &[Claim],
) -> Option<Proof> {
    // Cycle detection: if this goal is already an ancestor in the current
    // proof branch, we're in a loop — treat as a leaf or fail.
    if ancestors.iter().any(|a| claims_equiv(a, goal)) {
        if saturated.contains(goal) {
            return Some(Proof::leaf(goal.clone()));
        }
        return None;
    }
    let ancestors = {
        let mut v = ancestors.to_vec();
        v.push(goal.clone());
        v
    };

    fn is_symbolic(p: &PClaim) -> bool {
        matches!(
            p,
            PClaim::RatioEq(_, _) | PClaim::SegEq(_, _)
        )
    }
    // Deterministic iteration: witnesses are chosen from a lexicographically
    // sorted snapshot so rendered chains are stable across runs.
    let store_snapshot: Vec<Claim> = {
        let mut v = saturated.all();
        v.sort_by_key(|c| c.to_string());
        v
    };
    for rule in rules {
        let (structural, symbolic): (Vec<_>, Vec<_>) = rule
            .antecedents
            .iter()
            .enumerate()
            .partition(|(_, a)| !is_symbolic(a));

        for bind in match_pat(goal, &rule.consequent, &HashMap::new()) {
            // Join the structural antecedents over the saturated store.
            let mut cur: Vec<Bindings> = vec![bind];
            for ant in structural.iter().map(|(_, a)| *a) {
                let mut next: Vec<Bindings> = Vec::new();
                for b in &cur {
                    for f in &store_snapshot {
                        next.extend(match_pat(&f, ant, b));
                    }
                    if next.len() > MAX_BINDINGS {
                        break;
                    }
                }
                cur = next;
                if cur.is_empty() {
                    break;
                }
            }

            'binds: for bind in cur {
                let mut parts: Vec<(usize, Proof)> = Vec::new();
                // Structural witnesses — recurse to rebuild nested derivations
                // when the witness is itself derived (not an input fact).
                {
                    let mut probe = vec![bind.clone()];
                    let mut used_witnesses: std::collections::HashSet<String> = std::collections::HashSet::new();
                    for &(pos, ant) in &structural {
                        let mut witness: Option<Claim> = None;
                        let mut survived: Vec<Bindings> = Vec::new();
                        for b in &probe {
                            for f in &store_snapshot {
                                if used_witnesses.contains(&f.to_string()) {
                                    continue;
                                }
                                for nb in match_pat(&f, ant, b) {
                                    if witness.is_none() {
                                        witness = Some(f.clone());
                                    }
                                    survived.push(nb);
                                }
                            }
                        }
                        let w = match witness {
                            Some(w) => w,
                            None => {
                                // No fact matches this structural antecedent.
                                // Try to prove it by recursing backward — this
                                // allows rules like segment-bisector-median to
                                // derive IsMedian(Q2,BC) from ratio facts.
                                // Only try when all pattern vars are bound.
                                let inst = instantiate(ant, &bind);
                                if inst.has_unbound() || depth == 0 {
                                    continue 'binds;
                                }
                                if let Some(sub) = prove_rec(&inst, saturated, rules, base, depth - 1, &ancestors) {
                                    parts.push((pos, sub));
                                    continue;
                                }
                                continue 'binds;
                            }
                        };
                        used_witnesses.insert(w.to_string());
                        let sub = if base.contains(&w) || depth == 0 {
                            Proof::leaf(w)
                        } else {
                            prove_rec(&w, saturated, rules, base, depth - 1, &ancestors)
                                .unwrap_or_else(|| Proof::leaf(w.clone()))
                        };
                        parts.push((pos, sub));
                        probe = survived;
                        if probe.len() > MAX_BINDINGS {
                            probe.truncate(MAX_BINDINGS);
                        }
                    }
                }

                // Symbolic antecedents: fact or numeric derivation.
                for &(pos, ant) in &symbolic {
                    let inst = instantiate(ant, &bind);
                    if inst.has_unbound() {
                        continue 'binds;
                    }
                    if base.contains(&inst) {
                        parts.push((pos, Proof::leaf(inst)));
                        continue;
                    }
                    if let Some(np) = crate::symbolic::numeric_proof(&inst, base) {
                        parts.push((pos, np));
                        continue;
                    }
                    // Also try numeric derivation against saturated store
                    // (RatioEq facts derived by forward saturation may
                    // enable ratio-to-segment conversion).
                    if let Some(np) = crate::symbolic::numeric_proof(&inst, saturated) {
                        parts.push((pos, np));
                        continue;
                    }
                    if saturated.contains(&inst) {
                        parts.push((pos, Proof::leaf(inst)));
                        continue;
                    }
                    continue 'binds;
                }

                // Side conditions must hold as facts.
                let req_ok = rule.requires.iter().all(|req| {
                    let inst = instantiate(req, &bind);
                    !inst.has_unbound() && saturated.contains(&inst)
                });
                if req_ok {
                    parts.sort_by_key(|(pos, _)| *pos);
                    return Some(Proof {
                        claim: goal.clone(),
                        antecedents: parts.into_iter().map(|(_, p)| p).collect(),
                        rule: Some(rule.id),
                    });
                }
            }
        }
    }

    // Fall back to treating the goal as an established (derived) fact.
    if saturated.contains(goal) {
        return Some(Proof::leaf(goal.clone()));
    }
    // Try numeric/coordinate derivation as a last resort (including
    // ratio-to-segment conversion using saturated ratio facts).
    if crate::symbolic::numeric_solves(goal, saturated) {
        return Some(Proof::leaf(goal.clone()));
    }
    None
}

/// Flatten a proof into a `->` chain: `(prem1 && prem2) -> mid -> goal`.
/// Trivial numeric bookkeeping nodes (`square`, `sqrt`) are skipped so the
/// chain shows the meaningful steps, and duplicate premises are removed.
pub fn to_chain(p: &Proof) -> Vec<(String, bool)> {
    if p.antecedents.is_empty() {
        return vec![(p.claim.to_string(), true)];
    }
    let mut out: Vec<(String, bool)> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut emit = |out: &mut Vec<(String, bool)>, c: &Claim, is_premise: bool| {
        let s = c.to_string();
        if is_premise {
            if seen.insert(s.clone()) {
                out.push((s, true));
            }
        } else {
            out.push((s, false));
        }
    };
    fn walk(p: &Proof, emit: &mut impl FnMut(&mut Vec<(String, bool)>, &Claim, bool), out: &mut Vec<(String, bool)>) {
        if p.antecedents.is_empty() {
            emit(out, &p.claim, true);
            return;
        }
        for ant in &p.antecedents {
            walk(ant, emit, out);
        }
        match p.rule {
            Some("square") | Some("sqrt") => {}
            _ => emit(out, &p.claim, false),
        }
    }
    walk(p, &mut emit, &mut out);
    out
}

/// Render a proof as a compact chain using the language's `->` syntax. If
/// `final_display` is given it overrides the rendering of the final claim
/// (used to preserve the user's own spelling, e.g. `BD=DC`).
/// If the proof has multiple independent antecedent branches with their own
/// sub-proofs, each branch is rendered on its own line.
pub fn render_chain(p: &Proof, final_display: Option<&str>) -> String {
    // Check if root has multiple antecedents that each have their own premises
    let has_complex_branches = p.antecedents.len() > 1
        && p.antecedents.iter().all(|ant| !ant.antecedents.is_empty());

    if has_complex_branches {
        let mut lines = Vec::new();
        for ant in &p.antecedents {
            // Render each complex branch on its own line
            let sub_chain = render_chain(ant, None);
            lines.push(sub_chain);
        }
        // Final step combining the antecedents
        let final_claim = if let Some(d) = final_display { d.to_string() } else { p.claim.to_string() };
        let rule = p.rule.unwrap_or("");
        if !rule.is_empty() {
            lines.push(format!("({}) -> {}", p.antecedents.iter().map(|a| a.claim.to_string()).collect::<Vec<_>>().join(" && "), final_claim));
        } else {
            lines.push(final_claim);
        }
        return lines.join("\n");
    }

    // Single branch or simple multiple premises - original logic
    let chain = to_chain(p);
    let mut premises: Vec<String> = Vec::new();
    let mut conclusions: Vec<String> = Vec::new();
    for (i, (c, is_premise)) in chain.iter().enumerate() {
        let last = i == chain.len() - 1;
        let rendered = if last && final_display.is_some() {
            final_display.unwrap().to_string()
        } else {
            c.clone()
        };
        if *is_premise {
            premises.push(rendered);
        } else {
            conclusions.push(rendered);
        }
    }
    let mut parts: Vec<String> = Vec::new();
    if premises.is_empty() {
        if let Some(first) = conclusions.first() {
            parts.push(first.clone());
            conclusions = conclusions[1..].to_vec();
        }
    } else {
        let joined = premises.join(" && ");
        if premises.len() > 1 {
            parts.push(format!("({})", joined));
        } else {
            parts.push(joined);
        }
    }
    parts.extend(conclusions);
    parts.join(" -> ")
}

/// Render a proof as an indented tree for readability.
pub fn render_tree(p: &Proof, indent: usize, final_display: Option<&str>) -> String {
    let pad = "  ".repeat(indent);
    let mut out = String::new();
    let claim_display = if p.rule.is_some() && final_display.is_some() {
        final_display.unwrap().to_string()
    } else {
        p.claim.to_string()
    };
if p.rule.is_some() {
        out.push_str(&format!("{}{}\n", pad, claim_display));
        out.push_str(&format!("{}  by {}:\n", pad, p.rule.unwrap()));
    } else {
        out.push_str(&format!("{}{}  [fact]\n", pad, p.claim));
        return out;
    }
    for ant in &p.antecedents {
        out.push_str(&render_tree(ant, indent + 1, None));
    }
    out
}


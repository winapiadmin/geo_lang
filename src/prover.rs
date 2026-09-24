//! Backward-chaining prover.
//!
//! Given a goal claim, the prover searches the rule base for a chain of rule
//! applications whose premises are already established facts (leaves). The
//! resulting proof can be rendered both as a tree and as a single `->` chain
//! matching the language's proof-step syntax.

use crate::checker::{FactStore, Origin};
use crate::claim::{Claim, RatioAtom, RatioExpr};
use crate::rules::{instantiate, match_pat, Bindings, Rule, PClaim};
use std::collections::HashMap;

pub const MAX_DEPTH: usize = 16;

/// How many new facts the forward pass may derive per goal.
const MAX_SATURATION: usize = 200_000;
const MAX_SATURATION_DUMP: usize = 512;

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
    // A 3-letter triangle-style ref with a repeated point, e.g. "AAC" —
    // not a real triangle, and the actual source of the `IsSimilar(AAC,BCH)`
    // style junk seen in saturation dumps.
    fn deg_tri(s: &str) -> bool {
        let b = s.as_bytes();
        b.len() == 3 && (b[0] == b[1] || b[1] == b[2] || b[0] == b[2])
    }
    // A ratio atom is degenerate if it's a zero-length segment (repeated
    // point), e.g. the `AA` in `AA/BC`. Checked independently of what's on
    // the other side of the quotient or the other side of the equality —
    // `AA/BC = AC/BH` is just as meaningless as `AA/AA`, even though
    // neither side alone is a "unit ratio".
    fn deg_atom(a: &RatioAtom) -> bool {
        matches!(a, RatioAtom::Seg(s) if deg_seg(s))
    }
    fn deg_ratio_expr(e: &RatioExpr) -> bool {
        match e {
            RatioExpr::Seg(s) => deg_seg(s),
            RatioExpr::Quot { num, den } => deg_atom(num) || deg_atom(den),
        }
    }
    fn is_unit_ratio(e: &RatioExpr) -> bool {
        matches!(e, RatioExpr::Quot { num, den } if num == den)
    }
    match c {
        Claim::SegEq(a, b) => deg_seg(a) || deg_seg(b),
        Claim::TriEq(a, b) | Claim::AngleEq(a, b) => a == b || deg_tri(a) || deg_tri(b),
        Claim::RatioEq(lhs, rhs) => {
            deg_ratio_expr(lhs)
                || deg_ratio_expr(rhs)
                || (is_unit_ratio(lhs) && is_unit_ratio(rhs))
                || lhs == rhs
        }
        Claim::PredVal { name, args, .. } => {
            // Collinear with a repeated point is trivially true.
            if name == "iscollinear" && args.len() == 3 {
                let mut a = args.clone();
                a.sort();
                a.dedup();
                if a.len() < args.len() {
                    return true;
                }
            }
            // Similarity (and any other triangle-pair predicate) with a
            // degenerate triangle arg, e.g. `IsSimilar(AAC,BCH)`.
            if name == "issimilar" {
                if args.iter().any(|a| deg_tri(a)) {
                    return true;
                }
            }
            let seg_pred = matches!(
                name.as_str(),
                "isparallel" | "isperpendicular" | "ismedian" | "isaltitude"
            );
            if seg_pred && args.len() == 2 {
                if deg_seg(&args[0]) || deg_seg(&args[1]) {
                    return true;
                }
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
    saturate_toward(facts, rules, None, None)
}

/// Forward saturate with per-depth fact dumping.
/// When `dump_depth` is `Some(n)`, prints facts after each saturation depth up to `n`.
pub fn forward_saturate_d(facts: &FactStore, rules: &[Rule], dump_depth: Option<usize>) -> FactStore {
    saturate_toward(facts, rules, None, dump_depth)
}

/// Like [`forward_saturate`] but stops as soon as `goal` becomes derivable.
///
/// Semi-naive evaluation: after the first pass, a rule application only
/// contributes when at least one of its matches involves a fact derived in
/// the previous pass, which keeps later passes proportional to the delta.
pub fn saturate_toward(facts: &FactStore, rules: &[Rule], goal: Option<&Claim>, dump_depth: Option<usize>) -> FactStore {
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

    if dump_depth.is_some() {
        println!("=== depth 0: {} base facts ===", store.all().len());
        for c in store.all() {
            println!("  {}", c);
        }
    }

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
        let mut seen: std::collections::HashSet<Claim> = std::collections::HashSet::new();
        for (bind, dcount, _used) in cur {
            if !first_pass && dcount == 0 {
                continue;
            }
            // `requires` side conditions must already hold, but a clause may
            // reference a variable that no antecedent binds (e.g. a witness
            // point established independently, like `Q` in
            // medial-segment-midpoint's `requires: IsMedian(Q, Seg2(B,C))`).
            // Instantiating such a clause with an unbound variable renders it
            // as an empty-string placeholder (e.g. `IsMedian(,BC)`), which
            // `full_contains` can never find — silently failing every
            // binding forever. So: when a requires clause instantiates fully,
            // check it directly (fast path); when it still has an unbound
            // variable, join it against the store like a regular antecedent
            // to discover a value for that variable instead of rejecting.
            let mut req_binds: Vec<Bindings> = vec![bind];
            for req in &rule.requires {
                let mut next_binds = Vec::new();
                for b in &req_binds {
                    let inst = instantiate(req, b);
                    if !inst.has_unbound() {
                        if full_contains(idx, &inst) {
                            next_binds.push(b.clone());
                        }
                        continue;
                    }
                    let mut cands: Vec<&Claim> = Vec::new();
                    collect_shape_candidates(req, idx, &mut cands);
                    for f in &cands {
                        next_binds.extend(match_pat(f, req, b));
                    }
                }
                req_binds = next_binds;
                if req_binds.is_empty() {
                    break;
                }
            }
            for bind in req_binds {
                let c = instantiate(&rule.consequent, &bind);
                if !c.has_unbound() && !is_degenerate(&c) && seen.insert(c.clone()) {
                    out.push(c);
                }
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
            P::PredVal(n, a, _) => vec![format!("p|{}|{}", n.to_lowercase(), a.len())],
            P::PredAt(n, a, _) => vec![format!("p|{}|{}", n.to_lowercase(), a.len())],
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
                // RatioEq facts must not be numerically contradictory —
                // structural matching alone can produce spurious equalities
                // like AB/AB = AC/AH via trivial-ratio transitivity chains.
                // For most rules we still require full numeric confirmation
                // (`ratio_solves`), since loosening this broadly floods
                // ratio-transitivity with unverified facts and blows up
                // saturation combinatorially on unrelated problems.
                //
                // `metric-relations` and `angle-bisector-theorem` are a
                // narrow, deliberate exception: they're sound by
                // construction (directly instantiated from a matched
                // geometric rule, not chained), and for problems with no
                // given numeric lengths (e.g. a purely symbolic ratio
                // proof) `ratio_solves` can never confirm *any* ratio fact,
                // which silently blocks every proof that needs one of
                // these two rules. So for just these two, only reject on a
                // positive numeric *conflict* — nothing to conflict with
                // means nothing to reject.
                if let Claim::RatioEq(_, _) = c {
                    let lenient = matches!(
                        rule.id,
                        "metric-relations" | "angle-bisector-theorem"
                    );
                    if lenient {
                        if crate::symbolic::ratio_conflicts(&c, &store) {
                            continue;
                        }
                    } else if !crate::symbolic::ratio_solves(&c, &store) {
                        continue;
                    }
                }
if store.add(c.clone(), Origin::Proof(0, 0)) {
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
        // Cap explosive deltas (e.g. Iscollinear blowup) to keep saturation tractable.
        if delta.len() > MAX_SATURATION_DUMP {
            if dump_depth.is_some() {
                println!("=== depth {}: {} new facts, {} total (capped delta) ===", passes, delta.len(), store.all().len());
            }
            break;
        }
        if let Some(max_d) = dump_depth {
            if passes <= max_d {
                println!("=== depth {}: {} new facts, {} total ===", passes, delta.len(), store.all().len());
                for c in &delta {
                    println!("  + {}", c);
                }
            }
        }
        if store.all().len() > base + MAX_SATURATION {
            break;
        }
    }
    // Second pass: apply rules that were skipped in the main loop to produce
    // derived facts (AngleEq, RatioEq, On from IsMedian) needed by backward
    // chaining. These rules are kept separate because they can cause
    // combinatorial explosion if applied during the main saturation.
    // Only run if main loop didn't stabilize (delta not empty at end).
    // For now, skip to avoid timeout on prob12.
    // TODO: re-enable with proper delta tracking
    // {
    //     let skipped_ids: &[&str] = &[
    //         "subset-parallel", "subset-parallel-right",
    //         "midpoint-ratio", "midpoint-ratio-right",
    //         "similarity-proportional-sides", "similarity-proportional-sides-2", "similarity-proportional-sides-3",
    //         "parallel-corresponding-angles", "parallel-corresponding-angles-2",
    //         "ratio-double",
    //         "median-implies-on",
    //         "aa-similarity",
    //         "similarity-symmetry",
    //         "collinearity-via-midpoint",
    //         "segment-bisector-median",
    //         "ratio-same-denom-segeq",
    //         "ratio-same-denom-segeq-inv",
    //     ];
    //     let skipped_rules: Vec<&Rule> = rules.iter()
    //         .filter(|r| skipped_ids.iter().any(|id| r.id == *id))
    //         .collect();
    //     let mut delta: Vec<Claim> = store.all();
    //     let mut p2 = 0usize;
    //     while !delta.is_empty() && p2 < 2 {
    //         let current = store.all();
    //         let index = build_index(&current);
    //         let delta_set: std::collections::HashSet<Claim> = delta.iter().cloned().collect();
    //         let mut new_delta: Vec<Claim> = Vec::new();
    //         for rule in &skipped_rules {
    //             for c in join_rule(rule, &index, &delta_set, p2 == 0) {
    //                 if !store.contains(&c) {
    //                     store.add(c.clone(), Origin::Proof(0, 0));
    //                     new_delta.push(c.clone());
    //                 }
    //             }
    //         }
    //         delta = new_delta;
    //         p2 += 1;
    //     }
    // }
    // Checker-side closures may unlock new length equalities once derived
    // facts (e.g. circumcenter equidistance) exist; stabilize.
    while closure_runs < 2 {
        closure_runs += 1;
        let before = store.all().len();
        crate::checker::seg_eq_closure(&mut store);
        crate::checker::circle_membership_closure(&mut store);
        if store.all().len() == before {
            break;
        }
        let mut p2 = 0usize;
        delta = store.all();
        while !delta.is_empty() && p2 < 2 {
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
                    // RatioEq facts must be numerically valid — structural
                    // matching alone can produce spurious equalities like
                    // AB/AB = AC/AH via trivial-ratio transitivity chains.
                    if let Claim::RatioEq(_, _) = c {
                        if !crate::symbolic::ratio_solves(&c, &store) {
                            continue;
                        }
                    }
if store.add(c.clone(), Origin::Proof(0, 0)) {
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

    // AA-similarity: try to derive similarity from angle equalities
    // using shared rays and right angles.
    if let Some(p) = prove_similarity_aa(goal, facts) {
        return Some(p);
    }

    let saturated = saturate_toward(facts, rules, Some(goal), None);
    // Try symbolic (rule-based) proof first — prefers algebraic reasoning
    // over coordinate-based numeric computation.
    if let Some(p) = prove_inner(goal, &saturated, rules, facts, None) {
        return Some(p);
    }
    // Also try numeric proof against the saturated store, which may contain
    // RatioEq facts derived by forward chaining that the base facts lack.
    if let Some(p) = crate::symbolic::numeric_proof(goal, &saturated) {
        return Some(p);
    }
    None
}

/// Prove `goal` against a pre-computed saturated store (see
/// [`forward_saturate`]). Lets callers amortize one saturation across many
/// goals; falls back to the base facts for numeric derivations.
pub fn prove_seeded(
    goal: &Claim,
    facts: &FactStore,
    saturated: &FactStore,
    rules: &[Rule],
    disabled: Option<&std::collections::HashSet<&str>>,
) -> Option<Proof> {
    // Numeric / coordinate derivations run against the base facts first.
    if let Some(p) = crate::symbolic::numeric_proof(goal, facts) {
        return Some(p);
    }
    // AA-similarity: try to derive similarity from angle equalities.
    if let Some(p) = prove_similarity_aa(goal, facts) {
        return Some(p);
    }
    // Try symbolic (rule-based) proof first.
    if let Some(p) = prove_inner(goal, saturated, rules, facts, disabled) {
        return Some(p);
    }
    // Fall back to numeric / coordinate derivations.
    if let Some(p) = crate::symbolic::numeric_proof(goal, facts) {
        return Some(p);
    }
    if let Some(p) = crate::symbolic::numeric_proof(goal, saturated) {
        return Some(p);
    }
    None
}

/// Try to prove `IsSimilar(T1,T2)` via AA similarity.
///
/// Checks all 6 vertex correspondences and attempts to verify two pairs of
/// equal angles using:
/// 1. Existing `AngleEq` facts
/// 2. Shared-ray: `On(P, XY)` implies `Angle(ZXP) = Angle(ZXY)` for any Z
/// 3. Right angles: `Rightat(tri, V)` at corresponding vertices
pub fn prove_similarity_aa(goal: &Claim, facts: &FactStore) -> Option<Proof> {
    use crate::claim::Value;

    let (t1_str, t2_str) = match goal {
        Claim::PredVal { name, args, value }
            if name == "issimilar" && args.len() == 2 && *value == Value::Bool(true) =>
        {
            (args[0].clone(), args[1].clone())
        }
        _ => return None,
    };

    let chars1: Vec<char> = t1_str.chars().filter(|c| c.is_ascii_alphabetic()).collect();
    let chars2: Vec<char> = t2_str.chars().filter(|c| c.is_ascii_alphabetic()).collect();
    if chars1.len() != 3 || chars2.len() != 3 {
        return None;
    }

    let perms: Vec<Vec<usize>> = vec![
        vec![0, 1, 2], vec![0, 2, 1], vec![1, 0, 2],
        vec![1, 2, 0], vec![2, 0, 1], vec![2, 1, 0],
    ];

    let all = facts.all();

    // Collect On facts for shared-ray checks.
    let on_facts: Vec<(String, String, String)> = all.iter().filter_map(|c| {
        if let Claim::On(p, seg) = c {
            let cs: Vec<char> = seg.chars().collect();
            if cs.len() == 2 {
                Some((p.clone(), cs[0].to_string(), cs[1].to_string()))
            } else {
                None
            }
        } else {
            None
        }
    }).collect();

    // Collect Rightat facts.
    let right_at: Vec<(String, String)> = all.iter().filter_map(|c| {
        if let Claim::PredVal { name, args, value, .. } = c {
            if name == "rightat" && args.len() == 1 {
                if let Value::Point(v) = value {
                    return Some((args[0].clone(), v.clone()));
                }
            }
        }
        None
    }).collect();

    // Helper: check if a triangle has a right angle at a given vertex.
    fn has_right_at(tri: &str, vertex: &str, right_at: &[(String, String)]) -> bool {
        let mut tri_chars: Vec<char> = tri.to_lowercase().chars().collect();
        tri_chars.sort();
        let tri_sorted: String = tri_chars.into_iter().collect();
        for (t, v) in right_at {
            let mut t_chars: Vec<char> = t.to_lowercase().chars().collect();
            t_chars.sort();
            let t_sorted: String = t_chars.into_iter().collect();
            if t_sorted == tri_sorted && v.to_lowercase() == vertex.to_lowercase() {
                return true;
            }
        }
        false
    }

    // Helper: check if AngleEq(a,b) exists (in either order).
    fn has_angle_eq(a: &str, b: &str, all: &[Claim]) -> bool {
        let na = Claim::norm_angle(a);
        let nb = Claim::norm_angle(b);
        all.iter().any(|c| match c {
            Claim::AngleEq(x, y) => (*x == na && *y == nb) || (*x == nb && *y == na),
            _ => false,
        })
    }

    // Helper: build angle string for a triangle vertex.
    // Triangle "abc" with vertex at position idx (0-based), angle at vertex.
    fn tri_angle(tri: &[char], idx: usize) -> String {
        let v = tri[idx];
        let mut arms: Vec<String> = Vec::new();
        for (i, &c) in tri.iter().enumerate() {
            if i != idx {
                arms.push(c.to_lowercase().to_string());
            }
        }
        arms.sort();
        format!("{}{}{}", arms[0], v.to_lowercase(), arms[1])
    }

    // Try each correspondence.
    for perm in &perms {
        // For AA we need 2 of 3 angle pairs to match.
        let angle_pairs: Vec<(usize, usize)> = vec![
            (0, perm[0]),
            (1, perm[1]),
            (2, perm[2]),
        ];

        let mut matched_angles: Vec<(String, String, Proof)> = Vec::new();

        for &(i1, i2) in &angle_pairs {
            let a1 = tri_angle(&chars1, i1);
            let a2 = tri_angle(&chars2, i2);
            let na1 = Claim::norm_angle(&a1);
            let na2 = Claim::norm_angle(&a2);

            // Check 1: direct AngleEq fact.
            if has_angle_eq(&a1, &a2, &all) {
                matched_angles.push((
                    na1.clone(), na2.clone(),
                    Proof { claim: Claim::angle_eq(&a1, &a2), antecedents: vec![], rule: None },
                ));
                continue;
            }

            // Check 2: right angles at corresponding vertices.
            let v1 = chars1[i1].to_lowercase().to_string();
            let v2 = chars2[i2].to_lowercase().to_string();
            if has_right_at(&t1_str, &v1, &right_at)
                && has_right_at(&t2_str, &v2, &right_at)
            {
                let eq = Claim::angle_eq(&a1, &a2);
                matched_angles.push((
                    na1.clone(), na2.clone(),
                    Proof { claim: eq, antecedents: vec![], rule: Some("right-angles-equal") },
                ));
                continue;
            }

            // Check 3: shared ray from On(P, XY).
            // For Angle(ZX P) = Angle(ZX Y), we need On(P, XY) where X is
            // the vertex of the angle and P, Y are the arms.
            // The two angles share vertex chars1[i1] = chars2[i2] (the
            // correspondence vertex).
            // We need one arm to be the same point and the other arm to
            // lie on the same line through the vertex.
            let v = &chars1[i1].to_lowercase().to_string();
            let v_other = &chars2[i2].to_lowercase().to_string();
            if v != v_other { continue; }

            let arms1: Vec<String> = (0..3).filter(|&j| j != i1)
                .map(|j| chars1[j].to_lowercase().to_string()).collect();
            let arms2: Vec<String> = (0..3).filter(|&j| j != i2)
                .map(|j| chars2[j].to_lowercase().to_string()).collect();

            // Check if one arm is shared and the other two are collinear
            // through the vertex via On.
            // Shared arm + On(other2, vertex-other1)
            for a1_arm in &arms1 {
                for a2_arm in &arms2 {
                    if a1_arm == a2_arm {
                        // Found shared arm. Check the other arms.
                        let other1 = arms1.iter().find(|x| *x != a1_arm).unwrap();
                        let other2 = arms2.iter().find(|x| *x != a2_arm).unwrap();
                        // On(other2, v-other1) or On(other1, v-other2)
                        for (op, ox, oy) in &on_facts {
                            let seg_key = |a: &str, b: &str| {
                                let mut s = vec![a.to_string(), b.to_string()];
                                s.sort();
                                s.join("")
                            };
                            if op == other2 && seg_key(ox, oy) == seg_key(v, other1) {
                                let eq = Claim::angle_eq(&a1, &a2);
                                matched_angles.push((
                                    na1.clone(), na2.clone(),
                                    Proof { claim: eq, antecedents: vec![], rule: Some("shared-ray") },
                                ));
                                break;
                            }
                            if op == other1 && seg_key(ox, oy) == seg_key(v, other2) {
                                let eq = Claim::angle_eq(&a1, &a2);
                                matched_angles.push((
                                    na1.clone(), na2.clone(),
                                    Proof { claim: eq, antecedents: vec![], rule: Some("shared-ray") },
                                ));
                                break;
                            }
                        }
                    }
                }
                if matched_angles.len() >= 1 {
                    break;
                }
            }
            // Only count one match per angle pair.
            if matched_angles.iter().any(|(n1, n2, _)| *n1 == na1 && *n2 == na2) {
                continue;
            }
        }

        if matched_angles.len() >= 2 {
            return Some(Proof {
                claim: goal.clone(),
                antecedents: vec![
                    matched_angles[0].2.clone(),
                    matched_angles[1].2.clone(),
                ],
                rule: Some("aa-similarity"),
            });
        }
    }

    None
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
    disabled: Option<&std::collections::HashSet<&str>>,
) -> Option<Proof> {
    prove_rec(goal, saturated, rules, base, PROOF_DEPTH, &[], disabled)
}

fn prove_rec(
    goal: &Claim,
    saturated: &FactStore,
    rules: &[Rule],
    base: &FactStore,
    depth: usize,
    ancestors: &[Claim],
    disabled: Option<&std::collections::HashSet<&str>>,
) -> Option<Proof> {
    // Cycle detection: if this goal is already an ancestor in the current
    // proof branch, we're in a loop — treat as a leaf or fail.
    if ancestors.iter().any(|a| claims_equiv(a, goal)) {
        if saturated.contains(goal) && disabled.is_none() {
            return Some(Proof::leaf(goal.clone()));
        }
        return None;
    }
    let ancestors = {
        let mut v = ancestors.to_vec();
        v.push(goal.clone());
        v
    };

    // Prefer input facts over rules: if the goal is already an input
    // fact, return a leaf immediately — avoids complex rule-derived
    // proofs for facts that were given directly.
    if base.contains(goal) {
        return Some(Proof::leaf(goal.clone()));
    }

    // Note: goals present only in the saturated store (forward-derived, not
    // base inputs) are still searched for a rule-based proof first so the
    // derivation is rendered; a leaf fallback is used after the rule loop.

    fn is_symbolic(p: &PClaim) -> bool {
        matches!(
            p,
            PClaim::RatioEq(_, _) | PClaim::SegEq(_, _)
        )
    }
    /// True if every variable referenced by `p` is already bound in `bind`.
    /// SegEq/RatioEq antecedents with free vars (e.g. center `O` in
    /// `SegEq(Seg2(O,A),Seg2(O,B))`) must be joined structurally so those
    /// vars get bound from the store; treating them as purely symbolic
    /// would instantiate them with an empty `O` and never match.
    fn pattern_vars_bound(p: &PClaim, bind: &Bindings) -> bool {
        fn expr_vars(e: &crate::rules::PExpr, bind: &Bindings) -> bool {
            use crate::rules::PExpr as E;
            match e {
                E::PtVar(v) | E::AnyRef(v) => bind.contains_key(v),
                E::Seg2(a, b) => bind.contains_key(a) && bind.contains_key(b),
                E::Tri3(a, b, c) => {
                    bind.contains_key(a) && bind.contains_key(b) && bind.contains_key(c)
                }
                E::PtRef(_) | E::SegRef(_) | E::TriRef(_) => true,
            }
        }
        match p {
            PClaim::SegEq(a, b) | PClaim::TriEq(a, b) | PClaim::AngleEq(a, b) => {
                expr_vars(a, bind) && expr_vars(b, bind)
            }
            PClaim::RatioEq(l, r) => {
                fn ratio_bound(e: &crate::rules::PRatioExpr, bind: &Bindings) -> bool {
                    use crate::rules::{PRatioAtom, PRatioExpr as R};
                    fn atom_bound(a: &PRatioAtom, bind: &Bindings) -> bool {
                        match a {
                            PRatioAtom::Int(_) => true,
                            PRatioAtom::Expr(p) => expr_vars(p, bind),
                        }
                    }
                    match e {
                        R::Seg(p) => expr_vars(p, bind),
                        R::Int(_) => true,
                        R::Quot { num, den } => atom_bound(num, bind) && atom_bound(den, bind),
                    }
                }
                ratio_bound(l, bind) && ratio_bound(r, bind)
            }
            PClaim::PredVal(_, args, _) | PClaim::PredAt(_, args, _) => {
                args.iter().all(|a| expr_vars(a, bind))
            }
            PClaim::On(a, b) | PClaim::IsoscelesAt(a, b) => expr_vars(a, bind) && expr_vars(b, bind),
            PClaim::OnSameCircle(pts) => pts.iter().all(|p| expr_vars(p, bind)),
        }
    }
    // Deterministic iteration: witnesses are chosen from a lexicographically
    // sorted snapshot so rendered chains are stable across runs.
    let store_snapshot: Vec<Claim> = {
        let mut v = saturated.all();
        v.sort_by_key(|c| c.to_string());
        v
    };
    // Sort rules by complexity (fewer antecedents = simpler) so simpler
    // proofs are preferred over complex ones.
    let mut sorted_rules: Vec<&Rule> = rules.iter().collect();
    sorted_rules.sort_by_key(|r| r.antecedents.len());
    for rule in sorted_rules {
        // Disabled rules are excluded from the search. Any proof found below
        // must therefore come from facts or other enabled rules; never
        // fabricate a proof from the disabled rule's own premises.
        let is_disabled = disabled.map_or(false, |d| d.contains(rule.id));
        if is_disabled {
            if let Some(chain_str) = rule.chain {
                let steps = match crate::rule_loader::parse_fallback_chain(chain_str) {
                    Ok(steps) => steps,
                    Err(error) => {
                        eprintln!("fallback parse failed for {}: {}", rule.id, error);
                        continue;
                    }
                };
                if steps.is_empty() {
                    continue;
                }
                let final_step = &steps[steps.len() - 1];
                let mut matches = Vec::new();
                let mut initial = match_pat(goal, &rule.consequent, &HashMap::new());
                let candidates = saturated.all();
                for pattern in rule.antecedents.iter().chain(rule.requires.iter()) {
                    let mut next = Vec::new();
                    for bind in &initial {
                        for fact in &candidates {
                            next.extend(match_pat(fact, pattern, bind));
                        }
                    }
                    initial = next;
                    if initial.is_empty() {
                        break;
                    }
                }
                for bind in initial {
                    matches.extend(match_pat(goal, &steps[steps.len() - 1].claims[0], &bind));
                }
                for bind in matches {
                    let mut proofs = Vec::new();
                    let mut chain_facts = base.clone();
                    let mut chain_saturated = saturated.clone();
                    let mut valid = true;
                    for step in &steps[..steps.len() - 1] {
                        for pattern in &step.claims {
                            let claim = instantiate(pattern, &bind);
                            if claim.has_unbound() {
                                valid = false;
                                break;
                            }
                            let Some(proof) = prove_rec(
                                &claim,
                                &chain_saturated,
                                rules,
                                &chain_facts,
                                depth.saturating_sub(1),
                                &ancestors,
                                disabled,
                            ) else {
                                valid = false;
                                break;
                            };
                            if let Some(expected_rule) = &step.rule_id {
                                if proof.rule != Some(expected_rule.as_str()) {
                                    valid = false;
                                    break;
                                }
                            }
                            chain_facts.add(claim.clone(), Origin::Proof(0, 0));
                            chain_saturated.add(claim, Origin::Proof(0, 0));
                            proofs.push(proof);
                        }
                        if !valid {
                            break;
                        }
                    }
                    if valid {
                        let conclusion = instantiate(&final_step.claims[0], &bind);
                        if conclusion.has_unbound() || !claims_equiv(&conclusion, goal) {
                                valid = false;
                        }
                    }
                    if valid {
                        return Some(Proof {
                            claim: goal.clone(),
                            antecedents: proofs,
                            rule: Some("fallback-chain"),
                        });
                    }
                }
            }
            continue;
        }

        for bind in match_pat(goal, &rule.consequent, &HashMap::new()) {
// Partition per-bind: SegEq antecedents with still-free pattern vars
            // (e.g. center O in SegEq(Seg2(O,A),Seg2(O,B))) must join
            // structurally to bind them from facts. RatioEq is always
            // symbolic — its antecedents are numeric, never matched
            // structurally against the fact store.
            let (structural, symbolic): (Vec<_>, Vec<_>) = rule
                .antecedents
                .iter()
                .enumerate()
                .partition(|(_, a)| {
                    !is_symbolic(a)
                        || (matches!(a, PClaim::SegEq(..))
                            && !pattern_vars_bound(a, &bind))
                });
            // Join the structural antecedents over the saturated store.
            let mut cur: Vec<Bindings> = vec![bind.clone()];
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
                                if let Some(sub) = prove_rec(&inst, saturated, rules, base, depth - 1, &ancestors, disabled) {
                                    parts.push((pos, sub));
                                    continue;
                                }
                                continue 'binds;
                            }
                        };
                        used_witnesses.insert(w.to_string());
                        let sub = if base.contains(&w) {
                            Proof::leaf(w)
                        } else if depth == 0 {
                            continue 'binds;
                        } else if let Some(sub) =
                            prove_rec(&w, saturated, rules, base, depth - 1, &ancestors, disabled)
                        {
                            sub
                        } else {
                            continue 'binds;
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
    fn walk(p: &Proof, emit: &mut impl FnMut(&mut Vec<(String, bool)>, &Claim, bool), out: &mut Vec<(String, bool)>, is_root: bool) {
        if p.antecedents.is_empty() {
            emit(out, &p.claim, true);
            return;
        }
        for ant in &p.antecedents {
            walk(ant, emit, out, false);
        }
        match p.rule {
            // Skip trivial bookkeeping nodes, but always emit the root.
            Some("square") | Some("sqrt") if !is_root => {}
            _ => emit(out, &p.claim, false),
        }
    }
    walk(p, &mut emit, &mut out, true);
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

/// Render a proof as ordered, checkable proof steps.
///
/// Unlike `render_chain`, this preserves nested derivations as separate
/// steps, so a derived witness is established before it is used as a premise.
pub fn render_checkable_chain(p: &Proof, final_display: Option<&str>) -> String {
    fn walk(
        p: &Proof,
        final_display: Option<&str>,
        out: &mut Vec<String>,
        is_root: bool,
    ) {
        if p.antecedents.is_empty() {
            if is_root {
                out.push(
                    final_display
                        .map(str::to_owned)
                        .unwrap_or_else(|| p.claim.to_string()),
                );
            }
            return;
        }

        for antecedent in &p.antecedents {
            walk(antecedent, None, out, false);
        }

        let conclusion = if is_root {
            final_display
                .map(str::to_owned)
                .unwrap_or_else(|| p.claim.to_string())
        } else {
            p.claim.to_string()
        };
        let premises = p
            .antecedents
            .iter()
            .map(|antecedent| antecedent.claim.to_string())
            .collect::<Vec<_>>();
        if premises.len() == 1 {
            out.push(format!("{} -> {}", premises[0], conclusion));
        } else {
            out.push(format!("({}) -> {}", premises.join(" && "), conclusion));
        }
    }

    let mut steps = Vec::new();
    walk(p, final_display, &mut steps, true);
    steps.join("\n")
}

/// Render synthetic compound-identity proof nodes as active EqChain steps.
/// These nodes are stored as internal `Eqchain(...)` predicates because they
/// are not ordinary atomic claims, but their arguments are valid language
/// expressions and must remain visible in generated proofs.
pub fn render_compound_proof(p: &Proof, final_display: &str) -> String {
    let mut steps = Vec::new();
    for ant in &p.antecedents {
        if let Claim::PredVal { name, args, .. } = &ant.claim {
            if name.eq_ignore_ascii_case("eqchain") && args.len() == 1 {
                steps.push(args[0].clone());
            }
        }
    }
    steps.push(final_display.to_string());
    steps.join("\n")
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

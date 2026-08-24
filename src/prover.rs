//! Backward-chaining prover.
//!
//! Given a goal claim, the prover searches the rule base for a chain of rule
//! applications whose premises are already established facts (leaves). The
//! resulting proof can be rendered both as a tree and as a single `->` chain
//! matching the language's proof-step syntax.

use crate::checker::{FactStore, Origin};
use crate::claim::Claim;
use crate::rules::{instantiate, match_pat, Bindings, Rule};
use std::collections::{HashMap, HashSet};

pub const MAX_DEPTH: usize = 12;

/// How many new facts the forward pass may derive per goal.
const MAX_SATURATION: usize = 64;

/// All consequents `rule` can produce when every antecedent already matches a
/// fact (bounded, forward chaining).
fn forward_rule_consequents(rule: &Rule, facts: &[Claim]) -> Vec<Claim> {
    let mut cur = vec![Bindings::new()];
    for ant in &rule.antecedents {
        let mut next = Vec::new();
        for bind in &cur {
            for f in facts {
                next.extend(match_pat(f, ant, bind));
            }
        }
        cur = next;
        if cur.is_empty() {
            break;
        }
    }
    let mut out = Vec::new();
    for bind in cur {
        let mut ok = true;
        for req in &rule.requires {
            if !facts.contains(&instantiate(req, &bind)) {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let c = instantiate(&rule.consequent, &bind);
        if !c.has_unbound() && !facts.contains(&c) {
            out.push(c);
        }
    }
    out
}

/// Derive the closure of `facts` under `rules` (sound forward chaining), used
/// to seed the backward prover with facts that follow directly from the input.
pub fn forward_saturate(facts: &FactStore, rules: &[Rule]) -> FactStore {
    let mut store = FactStore::new();
    for f in facts.all() {
        store.add(f.clone(), Origin::Input);
    }
    let mut changed = true;
    while changed {
        changed = false;
        let current = store.all();
        for rule in rules {
            // Skip inverse rules (ratio -> parallel) to avoid cycles in forward saturation
            if rule.id.contains("invthales") {
                continue;
            }
            for c in forward_rule_consequents(rule, &current) {
                if store.add(c, Origin::Proof(0, 0)) {
                    changed = true;
                }
            }
        }
        if store.all().len() > facts.all().len() + MAX_SATURATION {
            break;
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
pub fn prove(
    goal: &Claim,
    facts: &FactStore,
    rules: &[Rule],
    depth: usize,
) -> Option<Proof> {
    prove_inner(goal, facts, rules, depth)
}

fn prove_inner(
    goal: &Claim,
    facts: &FactStore,
    rules: &[Rule],
    depth: usize,
) -> Option<Proof> {
    prove_inner_with_visited(goal, facts, rules, depth, &mut HashSet::new())
}

fn prove_inner_with_visited(
    goal: &Claim,
    facts: &FactStore,
    rules: &[Rule],
    depth: usize,
    visited: &mut HashSet<Claim>,
) -> Option<Proof> {
    if depth > MAX_DEPTH {
        return None;
    }
    if facts.contains(goal) {
        return Some(Proof::leaf(goal.clone()));
    }
    if visited.contains(goal) {
        return None; // Cycle detected
    }
    visited.insert(goal.clone());

    // Numeric derivations (lengths, ratios, Pythagoras) come before rules.
    if let Some(p) = crate::symbolic::numeric_proof(goal, facts) {
        visited.remove(goal);
        return Some(p);
    }

    for rule in rules {
        for bind in match_pat(goal, &rule.consequent, &HashMap::new()) {
            // Satisfy each antecedent, binding variables and building sub-proofs.
            let mut sub: Vec<Proof> = Vec::new();
            let mut cur_bind = bind;
            let mut ok = true;

            for ant in &rule.antecedents {
                // Try to bind the antecedent against an existing fact first.
                let mut bound_to_fact: Option<Claim> = None;
                for f in facts.all() {
                    let matches = match_pat(&f, ant, &cur_bind);
                    if let Some(b) = matches.first() {
                        cur_bind = b.clone();
                        bound_to_fact = Some(f.clone());
                        break;
                    }
                }
                if let Some(f) = bound_to_fact {
                    sub.push(Proof::leaf(f));
                    continue;
                }

                // Otherwise instantiate fully and try to prove recursively.
                let inst = instantiate(ant, &cur_bind);
                if inst.has_unbound() {
                    ok = false;
                    break;
                }
                match prove_inner_with_visited(&inst, facts, rules, depth + 1, visited) {
                    Some(p) => {
                        // Re-bind variables the recursive proof introduced.
                        let new_binds = match_pat(&p.claim, ant, &cur_bind);
                        match new_binds.first() {
                            Some(b) => cur_bind = b.clone(),
                            None => {
                                ok = false;
                                break;
                            }
                        }
                        sub.push(p);
                    }
                    None => {
                        ok = false;
                        break;
                    }
                }
            }

            if !ok {
                continue;
            }

            // Side conditions must already be established facts.
            let mut req_ok = true;
            for req in &rule.requires {
                let inst = instantiate(req, &cur_bind);
                if !facts.contains(&inst) {
                    req_ok = false;
                    break;
                }
            }
            if req_ok {
                visited.remove(goal);
                return Some(Proof {
                    claim: goal.clone(),
                    antecedents: sub,
                    rule: Some(rule.id),
                });
            }
        }
    }
    visited.remove(goal);
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
pub fn render_chain(p: &Proof, final_display: Option<&str>) -> String {
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
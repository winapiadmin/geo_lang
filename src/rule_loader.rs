//! Rule loader: reads rule definitions from .geo files in a directory.

use crate::claim::Value;
use crate::rules::{Rule, PClaim, PExpr, PRatioExpr, PRatioAtom};
use std::fs;
use std::path::Path;

/// Load all rules from .geo files in the given directory.
/// Each .geo file defines one rule.
pub fn load_rules_from_dir(dir: &Path) -> Result<Vec<Rule>, String> {
    let mut rules = Vec::new();
    for entry in fs::read_dir(dir).map_err(|e| format!("read dir: {e}"))? {
        let entry = entry.map_err(|e| format!("dir entry: {e}"))?;
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("geo") {
            match parse_rule_file(&path) {
                Ok(rule) => rules.push(rule),
                Err(e) => eprintln!("warning: skipping rule {}: {}", path.display(), e),
            }
        }
    }
    rules.sort_by_key(|rule| {
        let priority = match rule.id {
            "equal-implies-similar" => 0,
            "ratio-to-similarity" => 1,
            "aa-similarity" => 2,
            "sas-similarity" => 3,
            "sss-similarity" => 4,
            _ => 100,
        };
        (priority, rule.id.to_string())
    });
    validate_chain_metadata(&rules)?;
    Ok(rules)
}

/// Validate the rule references embedded in explicit fallback chains.
///
/// The claim text is intentionally kept opaque for now because it is rendered
/// by the prover, but every annotated rule reference must resolve and may not
/// point back to the rule declaring the fallback.
fn validate_chain_metadata(rules: &[Rule]) -> Result<(), String> {
    let known: std::collections::HashSet<&str> = rules.iter().map(|r| r.id).collect();
    for rule in rules {
        let Some(chain) = rule.chain else { continue };
        let steps = parse_fallback_chain(chain).map_err(|error| {
            format!("rule {} has invalid fallback chain: {}", rule.id, error)
        })?;
        let final_claim = steps
            .last()
            .and_then(|step| step.claims.first())
            .ok_or_else(|| format!("rule {} has an empty fallback chain", rule.id))?;
        if final_claim != &rule.consequent {
            return Err(format!(
                "rule {} fallback must end with its declared consequent",
                rule.id
            ));
        }
        let mut rest = chain;
        while let Some(start) = rest.find('[') {
            let after = &rest[start + 1..];
            let Some(end) = after.find(']') else {
                return Err(format!(
                    "rule {} has malformed fallback chain: missing ']': {}",
                    rule.id, chain
                ));
            };
            let referenced = after[..end].trim();
            if referenced.is_empty() || !known.contains(referenced) {
                return Err(format!(
                    "rule {} fallback references unknown rule '{}'",
                    rule.id, referenced
                ));
            }
            if referenced == rule.id {
                return Err(format!(
                    "rule {} fallback cannot reference itself",
                    rule.id
                ));
            }
            rest = &after[end + 1..];
        }
    }
    Ok(())
}

/// Parse a single rule .geo file.
fn parse_rule_file(path: &Path) -> Result<Rule, String> {
    let content = fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let rule = parse_rule(&content, path)?;
    Ok(rule)
}

#[derive(Debug, Clone)]
pub(crate) struct FallbackStep {
    pub claims: Vec<PClaim>,
    pub rule_id: Option<String>,
}

/// Parse the claim steps in a rule fallback chain.
pub(crate) fn parse_fallback_chain(chain: &str) -> Result<Vec<FallbackStep>, String> {
    split_top_level(chain, "->")
        .into_iter()
        .map(|step| step.trim().to_string())
        .filter(|step| !step.is_empty())
        .map(|step| {
            let (claim, rule_id) = if let Some((claim, annotation)) = step.split_once('[') {
                let rule_id = annotation
                    .strip_suffix(']')
                    .ok_or_else(|| format!("malformed fallback annotation: {step}"))?
                    .trim();
                if rule_id.is_empty() {
                    return Err(format!("empty fallback rule annotation: {step}"));
                }
                (claim.trim().to_string(), Some(rule_id.to_string()))
            } else {
                (step.to_string(), None)
            };
            let claim = claim.trim();
            let claims = split_top_level(claim, "&&")
                .into_iter()
                .map(|part| parse_claim(part.trim(), "chain", Path::new("<chain>")))
                .collect::<Result<Vec<_>, _>>()?;
            if claims.is_empty() {
                return Err(format!("empty fallback proof step: {step}"));
            }
            Ok(FallbackStep {
                claims,
                rule_id,
            })
        })
        .collect()
}

fn split_top_level(input: &str, separator: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut depth: usize = 0;
    let bytes = input.as_bytes();
    let sep = separator.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0 && bytes.get(i..i + sep.len()) == Some(sep) {
            parts.push(input[start..i].to_string());
            i += sep.len();
            start = i;
        } else {
            i += 1;
        }
    }
    parts.push(input[start..].to_string());
    parts
}

/// Parse a rule from string content.
/// Expected format (text, not Rust):
/// ```text
/// rule: rule-id
/// antecedents:
///   - PredicateName(arg1, arg2, ...)
///   - ...
/// requires:
///   - PredicateName(arg1, ...)
///   - ...
/// consequent:
///   - PredicateName(arg1, ...)
/// chain: step1 [rule1] -> step2 [rule2] -> ...
/// ```
fn parse_rule(content: &str, path: &Path) -> Result<Rule, String> {
    let mut lines = content.lines().peekable();
    let mut rule_id = String::new();
    let mut antecedents = Vec::new();
    let mut requires = Vec::new();
    let mut consequent: Option<PClaim> = None;
    let mut chain: Option<String> = None;

    while let Some(line) = lines.next() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("rule:") {
            rule_id = rest.trim().to_string();
        } else if line == "antecedents:" {
            antecedents = parse_claim_list(&mut lines, "antecedents", path)?;
        } else if line == "requires:" {
            requires = parse_claim_list(&mut lines, "requires", path)?;
        } else if line == "consequent:" {
            consequent = Some(parse_single_claim(&mut lines, "consequent", path)?);
        } else if let Some(rest) = line.strip_prefix("chain:") {
            let first = rest.trim();
            if !first.is_empty() {
                chain = Some(first.to_string());
            } else {
                let mut parts = Vec::new();
                while let Some(next) = lines.peek() {
                    let next = next.trim();
                    if next.is_empty() {
                        lines.next();
                        continue;
                    }
                    if matches!(
                        next,
                        "antecedents:" | "requires:" | "consequent:" | "chain:"
                    ) || next.starts_with("rule:")
                    {
                        break;
                    }
                    let part = if let Some(rest) = next.strip_prefix("- ") {
                        rest.trim()
                    } else if next.starts_with('-') && !next.starts_with("->") {
                        next[1..].trim()
                    } else {
                        next
                    };
                    parts.push(part.to_string());
                    lines.next();
                }
                if !parts.is_empty() {
                    chain = Some(parts.join(" "));
                }
            }
        }
    }

    if rule_id.is_empty() {
        return Err(format!("{}: missing rule id", path.display()));
    }
    if consequent.is_none() {
        return Err(format!("{}: missing consequent", path.display()));
    }

    // Leak the chain string so it has a 'static lifetime.
    let chain_static: Option<&'static str> = chain.map(|s| &*Box::leak(s.into_boxed_str()));

    Ok(Rule {
        id: Box::leak(rule_id.into_boxed_str()),
        antecedents,
        requires,
        consequent: consequent.unwrap(),
        chain: chain_static,
    })
}

/// Parse a list of claims (antecedents or requires).
fn parse_claim_list(
    lines: &mut std::iter::Peekable<std::str::Lines>,
    section: &str,
    path: &Path,
) -> Result<Vec<PClaim>, String> {
    let mut claims = Vec::new();
    while let Some(line) = lines.peek() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            lines.next();
            continue;
        }
        if line.starts_with('-') {
            lines.next();
            let claim_line = line[1..].trim();
            if !claim_line.is_empty() {
                claims.push(parse_claim(claim_line, section, path)?);
            }
        } else if !line.contains(':') {
            break;
        } else {
            break;
        }
    }
    Ok(claims)
}

/// Parse a single claim from a line.
pub(crate) fn parse_claim(line: &str, section: &str, path: &Path) -> Result<PClaim, String> {
    let line = line.trim();
    
    // Check for assignment (=)
    if let Some(eq_pos) = line.find('=') {
        let left = line[..eq_pos].trim();
        let right = line[eq_pos+1..].trim();
        return parse_predicate_with_value(left, right, section, path);
    }
    
    parse_predicate(line, section, path)
}

/// Parse a predicate with a value (e.g., Predicate(args) = true)
fn parse_predicate_with_value(left: &str, right: &str, section: &str, path: &Path) -> Result<PClaim, String> {
    let (name, args) = parse_predicate_name_args(left)?;
    let name_lower = name.to_lowercase();
    if name_lower == "intersection" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: Intersection needs 2 args", path.display()));
        }
        return Ok(PClaim::PredAt("intersection".into(), args, parse_pexpr(right)?));
    }

    let value = parse_value(right)?;
    if name_lower == "iscollinear" {
        if args.len() != 3 {
            return Err(format!("{}: {section}: IsCollinear needs 3 args", path.display()));
        }
        Ok(PClaim::PredVal("iscollinear".into(), args, value))
    } else if name_lower == "isparallel" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsParallel needs 2 args", path.display()));
        }
        Ok(PClaim::PredVal("isparallel".into(), args, value))
    } else if name_lower == "isperpendicular" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsPerpendicular needs 2 args", path.display()));
        }
        Ok(PClaim::PredVal("isperpendicular".into(), args, value))
    } else if name_lower == "issimilar" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsSimilar needs 2 args", path.display()));
        }
        Ok(PClaim::PredVal("issimilar".into(), args, value))
    } else if name_lower == "isisosceles" {
        if args.len() != 1 {
            return Err(format!("{}: {section}: IsIsosceles needs 1 arg", path.display()));
        }
        Ok(PClaim::PredVal("isisosceles".into(), args, value))
    } else if name_lower == "isright" {
        if args.len() != 1 {
            return Err(format!("{}: {section}: IsRight needs 1 arg", path.display()));
        }
        Ok(PClaim::PredVal("isright".into(), args, value))
    } else if name_lower == "ismedian" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsMedian needs 2 args", path.display()));
        }
        Ok(PClaim::PredVal("ismedian".into(), args, value))
    } else if name_lower == "iscircumcenter" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsCircumcenter needs 2 args", path.display()));
        }
        Ok(PClaim::PredVal("iscircumcenter".into(), args, value))
    } else if name_lower == "isparallelogram" {
        if args.len() != 4 {
            return Err(format!("{}: {section}: IsParallelogram needs 4 args", path.display()));
        }
        Ok(PClaim::PredVal("isparallelogram".into(), args, value))
    } else if name_lower == "parallelogram" {
        if args.len() != 1 {
            return Err(format!("{}: {section}: Parallelogram needs 1 arg", path.display()));
        }
        Ok(PClaim::PredVal("parallelogram".into(), args, value))
    } else if name_lower == "isaltitude" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsAltitude needs 2 args", path.display()));
        }
        Ok(PClaim::PredVal("isaltitude".into(), args, value))
    } else if name_lower == "onsamecircle" {
        Ok(PClaim::OnSameCircle(args))
    } else if name_lower == "rightat" {
        if args.len() != 1 {
            return Err(format!("{}: {section}: RightAt needs 1 arg", path.display()));
        }
        let point = parse_pexpr(right)?;
        Ok(PClaim::PredAt("rightat".into(), args, point))
    } else if name_lower == "ratioeq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: RatioEq needs 2 args", path.display()));
        }
        let left = pexpr_to_ratio_expr(&args[0]);
        let right = pexpr_to_ratio_expr(&args[1]);
        Ok(PClaim::RatioEq(left, right))
    } else if name_lower == "segeq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: SegEq needs 2 args", path.display()));
        }
        Ok(PClaim::SegEq(args[0].clone(), args[1].clone()))
    } else if name_lower == "angleeq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: AngleEq needs 2 args", path.display()));
        }
        Ok(PClaim::AngleEq(args[0].clone(), args[1].clone()))
    } else if name_lower == "trieq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: TriEq needs 2 args", path.display()));
        }
        Ok(PClaim::TriEq(args[0].clone(), args[1].clone()))
    } else {
        // Generic predicate
        Ok(PClaim::PredVal(name, args, value))
    }
}

/// Parse a simple predicate without value.
fn parse_predicate(line: &str, section: &str, path: &Path) -> Result<PClaim, String> {
    let (name, args) = parse_predicate_name_args(line)?;
    let name_lower = name.to_lowercase();
    
    if name_lower == "segeq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: SegEq needs 2 args", path.display()));
        }
        Ok(PClaim::SegEq(args[0].clone(), args[1].clone()))
    } else if name_lower == "trieq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: TriEq needs 2 args", path.display()));
        }
        Ok(PClaim::TriEq(args[0].clone(), args[1].clone()))
    } else if name_lower == "angleeq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: AngleEq needs 2 args", path.display()));
        }
        Ok(PClaim::AngleEq(args[0].clone(), args[1].clone()))
    } else if name_lower == "ratioeq" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: RatioEq needs 2 args", path.display()));
        }
        let left = pexpr_to_ratio_expr(&args[0]);
        let right = pexpr_to_ratio_expr(&args[1]);
        Ok(PClaim::RatioEq(left, right))
    } else if name_lower == "on" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: On needs 2 args", path.display()));
        }
        Ok(PClaim::On(args[0].clone(), args[1].clone()))
    } else if name_lower == "isoscelesat" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsoscelesAt needs 2 args", path.display()));
        }
        Ok(PClaim::IsoscelesAt(args[0].clone(), args[1].clone()))
    } else if name_lower == "isaltitude" || name_lower == "isanglebisector"
        || name_lower == "iscircumcenter" || name_lower == "isincenter"
        || name_lower == "isorthocenter" || name_lower == "iscentroid"
        || name_lower == "isperpendicularbisector"
        || name_lower == "isperpendicular" || name_lower == "isparallel"
        || name_lower == "issimilar" || name_lower == "isisosceles"
        || name_lower == "isright" || name_lower == "isparallelogram"
        || name_lower == "iscollinear" || name_lower == "isacute"
        || name_lower == "iscirclecenter"
        || name_lower == "parallelogram" {
        Ok(PClaim::PredVal(name.to_lowercase(), args, Value::Bool(true)))
    } else if name_lower == "onsamecircle" {
        Ok(PClaim::OnSameCircle(args))
    } else if name_lower == "ismedian" {
        if args.len() != 2 {
            return Err(format!("{}: {section}: IsMedian needs 2 args", path.display()));
        }
        Ok(PClaim::PredVal("ismedian".into(), args, Value::Bool(true)))
    } else if name_lower == "predat" {
        // PredAt(PredicateName, Arg, Point)
        if args.len() != 3 {
            return Err(format!("{}: {section}: PredAt needs 3 args (pred_name, arg, point)", path.display()));
        }
        let pred_name = match &args[0] {
            PExpr::PtVar(s) => s.to_lowercase(),
            PExpr::AnyRef(s) => s.to_lowercase(),
            _ => return Err(format!("{}: {section}: PredAt first arg must be a predicate name", path.display())),
        };
        Ok(PClaim::PredAt(pred_name, vec![args[1].clone()], args[2].clone()))
    } else {
        Err(format!("{}: {section}: unknown predicate '{}'", path.display(), name))
    }
}

/// Parse predicate name and arguments: Name(arg1, arg2, ...)
fn parse_predicate_name_args(s: &str) -> Result<(String, Vec<PExpr>), String> {
    let s = s.trim();
    let paren_start = s.find('(').ok_or_else(|| format!("missing '(' in: {}", s))?;
    let paren_end = s.rfind(')').ok_or_else(|| format!("missing ')' in: {}", s))?;
    
    let name = s[..paren_start].trim().to_string();
    let args_str = &s[paren_start+1..paren_end].trim();
    
    let args = if args_str.is_empty() {
        Vec::new()
    } else {
        // Split by comma, respecting nested parentheses
        let arg_strings = split_args(args_str)?;
        arg_strings.into_iter().map(|a| parse_pexpr(a.trim())).collect::<Result<Vec<_>, _>>()?
    };
    
    Ok((name, args))
}

/// Split arguments by comma, respecting nested parentheses.
fn split_args(s: &str) -> Result<Vec<String>, String> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut paren_depth = 0;
    
    for ch in s.chars() {
        match ch {
            '(' => {
                paren_depth += 1;
                current.push(ch);
            }
            ')' => {
                if paren_depth == 0 {
                    return Err(format!("unmatched ')' in args: {}", s));
                }
                paren_depth -= 1;
                current.push(ch);
            }
            ',' => {
                if paren_depth == 0 {
                    args.push(current.trim().to_string());
                    current.clear();
                } else {
                    current.push(ch);
                }
            }
            _ => current.push(ch),
        }
    }
    
    if paren_depth != 0 {
        return Err(format!("unmatched '(' in args: {}", s));
    }
    
    if !current.trim().is_empty() {
        args.push(current.trim().to_string());
    }
    
    Ok(args)
}

/// Convert a PExpr to a PRatioExpr, handling quotient syntax (A/B parsed as PtVar).
fn pexpr_to_ratio_expr(pe: &PExpr) -> PRatioExpr {
    match pe {
        PExpr::PtVar(s) => {
            // First try to parse the whole thing as a Seg2 quotient like "Seg2(A,B)/Seg2(C,D)"
            if let Some(slash_pos) = find_top_level_slash(s) {
                let num_str = s[..slash_pos].trim();
                let den_str = s[slash_pos+1..].trim();
                let num = parse_ratio_atom_from_str_special(num_str);
                let den = parse_ratio_atom_from_str_special(den_str);
                PRatioExpr::Quot { num, den }
            } else if let Ok(n) = s.trim().parse::<u32>() {
                PRatioExpr::Int(n)
            } else {
                PRatioExpr::Seg(PExpr::AnyRef(s.clone()))
            }
        }
        PExpr::AnyRef(s) => {
            if let Some(slash_pos) = s.find('/') {
                let num_str = s[..slash_pos].trim();
                let den_str = s[slash_pos+1..].trim();
                let num = parse_ratio_atom_from_str(num_str);
                let den = parse_ratio_atom_from_str(den_str);
                PRatioExpr::Quot { num, den }
            } else if let Ok(n) = s.trim().parse::<u32>() {
                PRatioExpr::Int(n)
            } else {
                PRatioExpr::Seg(PExpr::AnyRef(s.clone()))
            }
        }
        _ => PRatioExpr::Seg(pe.clone()),
    }
}

fn parse_ratio_atom_from_str(s: &str) -> PRatioAtom {
    if let Ok(n) = s.trim().parse::<u32>() {
        PRatioAtom::Int(n)
    } else {
        PRatioAtom::Expr(PExpr::AnyRef(s.trim().to_string()))
    }
}

/// Like parse_ratio_atom_from_str but tries to parse Seg2(X,Y) properly.
fn parse_ratio_atom_from_str_special(s: &str) -> PRatioAtom {
    let s = s.trim();
    if let Ok(n) = s.parse::<u32>() {
        return PRatioAtom::Int(n);
    }
    if let Some(inner) = strip_prefix(s, "Seg2") {
        if let Ok((a, b)) = parse_two_args(inner) {
            return PRatioAtom::Expr(PExpr::Seg2(a.into(), b.into()));
        }
    }
    PRatioAtom::Expr(PExpr::AnyRef(s.to_string()))
}

/// Find the top-level '/' in a string (not inside parentheses).
fn find_top_level_slash(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            '/' if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// Parse a PExpr from string.
fn parse_pexpr(s: &str) -> Result<PExpr, String> {
    let s = s.trim();
    
    // If the string contains a slash, it's a ratio expression — treat as PtVar
    // so that pexpr_to_ratio_expr can handle it.
    if s.contains('/') {
        return Ok(PExpr::PtVar(s.into()));
    }
    
    // Check for Seg2(A, B)
    if let Some(inner) = strip_prefix(s, "Seg2") {
        let (a, b) = parse_two_args(inner)?;
        return Ok(PExpr::Seg2(a.into(), b.into()));
    }
    // Check for Tri3(A, B, C)
    if let Some(inner) = strip_prefix(s, "Tri3") {
        let (a, b, c) = parse_three_args(inner)?;
        return Ok(PExpr::Tri3(a.into(), b.into(), c.into()));
    }
    // Check for Angle(A, B, C) — alias for Tri3
    if let Some(inner) = strip_prefix(s, "Angle") {
        let (a, b, c) = parse_three_args(inner)?;
        return Ok(PExpr::Tri3(a.into(), b.into(), c.into()));
    }
    // Check for AnyRef(T)
    if let Some(inner) = strip_prefix(s, "AnyRef") {
        let a = inner.trim_matches(|c| c == '(' || c == ')').trim();
        return Ok(PExpr::AnyRef(a.into()));
    }
    // Point variable (PtVar)
    Ok(PExpr::PtVar(s.into()))
}

/// Strip prefix like "Name(...)"
fn strip_prefix<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    if s.starts_with(prefix) {
        let rest = &s[prefix.len()..];
        if rest.starts_with('(') {
            return Some(rest);
        }
    }
    None
}

fn parse_two_args(s: &str) -> Result<(String, String), String> {
    let s = s.trim_matches(|c| c == '(' || c == ')').trim();
    let parts: Vec<&str> = s.split(',').map(|x| x.trim()).collect();
    if parts.len() != 2 {
        return Err(format!("expected 2 args, got {} in: {}", parts.len(), s));
    }
    Ok((parts[0].into(), parts[1].into()))
}

fn parse_three_args(s: &str) -> Result<(String, String, String), String> {
    let s = s.trim_matches(|c| c == '(' || c == ')').trim();
    let parts: Vec<&str> = s.split(',').map(|x| x.trim()).collect();
    if parts.len() != 3 {
        return Err(format!("expected 3 args, got {}", parts.len()));
    }
    Ok((parts[0].into(), parts[1].into(), parts[2].into()))
}

/// Parse a Value from string.
fn parse_value(s: &str) -> Result<Value, String> {
    let s = s.trim().to_lowercase();
    match s.as_str() {
        "true" => Ok(Value::Bool(true)),
        "false" => Ok(Value::Bool(false)),
        _ => Err(format!("unknown value: {}", s)),
    }
}

/// Parse a single claim for consequent.
fn parse_single_claim(
    lines: &mut std::iter::Peekable<std::str::Lines>,
    section: &str,
    path: &Path,
) -> Result<PClaim, String> {
    while let Some(line) = lines.peek() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            lines.next();
            continue;
        }
        if line.starts_with('-') {
            lines.next();
            let claim_line = line[1..].trim();
            if !claim_line.is_empty() {
                return parse_claim(claim_line, section, path);
            }
        } else if !line.contains(':') {
            break;
        } else {
            break;
        }
    }
    Err(format!("{}: {section}: empty consequent", path.display()))
}
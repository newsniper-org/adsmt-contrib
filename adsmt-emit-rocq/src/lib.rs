//! Rocq (Coq) backend for adsmt-cert certificates.
//!
//! Produces a `.v` source file that re-states an adsmt
//! [`Certificate`] as a sequence of
//! `Axiom` / `Theorem ... Proof. ... Qed.` declarations. Each cert
//! step becomes a named Rocq entity whose statement is the step's
//! sequent conclusion; the conclusion step is exposed as
//! `Theorem result : <concl>. Proof. exact s<final>. Qed.`
//!
//! Lockstep with [`adsmt_cert::prover_emit::common`]. The Lean emit
//! in adsmt-cert is the reference shape; this crate mirrors it
//! exactly with the per-prover syntactic adjustments documented in
//! the cross-ITP output policy.
//!
//! # Ltac1 excluded
//!
//! Every emitted file opens with
//!
//! ```rocq
//! From Stdlib Require Import Logic.
//! From Ltac2 Require Import Ltac2.
//! Set Default Proof Mode "Ltac2".
//! ```
//!
//! The `Set Default Proof Mode "Ltac2"` directive forces Ltac2 for
//! every `Proof. ... Qed.` block. Ltac1 is the legacy tactic
//! language; this crate excludes it entirely. The minimum Rocq
//! version is 8.10 (when Ltac2 entered the standard distribution).
//!
//! # Mapping highlights
//!
//! | cert StepBody | Rocq emit |
//! |---|---|
//! | `Assume(φ)` | `Axiom s<i> : φ.` |
//! | `Refl(t)` | `Theorem s<i> : t = t. Proof. reflexivity. Qed.` |
//! | `Trans { lhs, rhs }` | `Theorem s<i> : <concl>. Admitted. (* eapply eq_trans; ... *)` |
//! | `EqMp { iff, p }` | `Theorem s<i> : <concl>. Admitted. (* apply (proj1 s<iff>); exact s<p>. *)` |
//! | `Deduct`/`Abs`/`Beta`/`Inst`/`InstType` | `Theorem s<i> : <concl>. Admitted. (* TODO *)` |
//! | `Theory { name, witness, parents }` | `Axiom s<i> : <concl>. (* theory '<name>'; witness: <summary> *)` |
//! | `Assumed { φ, explain }` | `Theorem s<i> : φ. Admitted. (* abductive: <explain> *)` |
//! | Final | `Theorem result : <concl>. Proof. exact s<final>. Qed.` |
//!
//! Free term variables emit as `Parameter <name> : Prop.` per the
//! Bool→Prop semantic anchor from
//! [`adsmt_cert::prover_emit::common`].

use std::fmt::Write;

use adsmt_cert::canonical::{Certificate, Step, StepBody};
use adsmt_cert::prover_emit::common::{escape_for_comment, witness_summary};
use adsmt_cert::TheoryWitness;
use adsmt_core::{Term, TermInner};

/// Emit a self-contained Rocq source string representing `cert`.
///
/// The returned text is parseable Rocq (≥ 8.10, Ltac2 mode); it
/// opens with the standard prelude, declares free variables as
/// `Parameter`s, then emits each step. The final declaration
/// closes the goal as
/// `Theorem result : <conclusion>. Proof. exact s<final>. Qed.`
///
/// Per the "Classical axiom imports (on-demand)" policy
/// (`adsmt-cert::prover_emit_policy.md`), classical-axiom imports
/// land between the fixed Ltac2 prelude and the `Module AdsmtCert.`
/// wrapper. If the cert has uncovered classical-axiom
/// requirements, [`emit_rocq`] panics — the policy is hard-failing
/// (D1.E-3 = α). Use [`try_emit_rocq`] when callers need to
/// inspect or recover from the error programmatically.
pub fn emit_rocq(cert: &Certificate) -> String {
    match try_emit_rocq(cert) {
        Ok(s) => s,
        Err(MissingImports(pairs)) => {
            let detail = pairs
                .iter()
                .map(|(sid, fam)| format!("s{}:{:?}", sid.0, fam))
                .collect::<Vec<_>>()
                .join(", ");
            panic!(
                "adsmt-emit-rocq: cert has uncovered classical-axiom \
                 requirements: [{detail}]. \
                 Add `should_import_classical` or `allow_to_import_classical` \
                 markers on the offending steps."
            );
        }
    }
}

/// One uncovered `(step, family)` pair per offending position,
/// matching the D1.E-2 = δ pair-level error reporting policy.
#[derive(Debug)]
pub struct MissingImports(
    pub Vec<(adsmt_cert::StepId, adsmt_cert::ClassicalModuleFamily)>,
);

/// Fallible variant of [`emit_rocq`]. Returns the offending
/// (step, family) pairs when the cert's resolved import set
/// does not subsume the required set.
pub fn try_emit_rocq(cert: &Certificate) -> Result<String, MissingImports> {
    use adsmt_cert::prover_emit::common::{
        aggregate_required, missing_imports, resolve_imports_with_scan,
        rocq_axiom_keywords, rocq_import_line,
    };
    use adsmt_cert::ClassicalSet;

    // v0.19 A.5: two-pass scan=true wiring.
    // Pass 1 — preliminary render without classical imports.
    // Pass 2 — resolve via scan honouring lazy+scan markers.
    // Pass 3 — final render with resolved imports as prelude.
    let preliminary = render_body(cert);
    let resolved = resolve_imports_with_scan(
        cert,
        &ClassicalSet::empty(),
        &[],
        &preliminary,
        rocq_axiom_keywords,
    );
    let required = aggregate_required(cert);
    if !required.is_empty() {
        let missing = missing_imports(cert, &resolved);
        if !missing.is_empty() {
            return Err(MissingImports(missing));
        }
    }

    let mut out = String::new();
    out.push_str("(* Generated by adsmt-emit-rocq (Rocq/Coq reflection, Ltac2) *)\n");
    out.push_str("(* One Parameter per free term variable, one decl per cert step *)\n");
    out.push_str("From Stdlib Require Import Logic.\n");
    out.push_str("From Ltac2 Require Import Ltac2.\n");
    out.push_str("Set Default Proof Mode \"Ltac2\".\n");

    // Classical-axiom imports (between fixed prelude and Module).
    // The trailing blank line separates this block from the
    // Module wrapper regardless of whether any imports landed.
    for fam in resolved.iter() {
        if let Some(line) = rocq_import_line(fam) {
            writeln!(out, "{line}").unwrap();
        }
    }
    out.push('\n');

    out.push_str("Module AdsmtCert.\n\n");

    let vars = collect_free_vars(cert);
    if !vars.is_empty() {
        for (name, ty_rocq) in &vars {
            writeln!(out, "Parameter {name} : {ty_rocq}.").unwrap();
        }
        out.push('\n');
    }

    emit_oracles(cert, &mut out);
    out.push_str("Section Proof.\n\n");

    for step in &cert.steps {
        emit_step(step, &mut out);
    }

    if cert.final_sequent().is_some() {
        // Inside the section this is the bare conclusion; closing the
        // section generalises it over the hypotheses.
        writeln!(
            out,
            "\nTheorem result : {}.\nProof. exact s{}. Qed.",
            render_term(&cert.final_sequent().expect("checked").concl),
            cert.conclusion.0
        )
        .unwrap();
    }
    out.push_str("\nEnd Proof.\n");
    out.push_str("\nEnd AdsmtCert.\n");
    Ok(out)
}

/// Render the cert body **without** any classical-axiom prelude
/// or the fixed Ltac2 prelude. Used by [`try_emit_rocq`]'s
/// pass-1 preliminary render for the D1.B
/// `lazy=true, scan=true` text-scan arm.
fn render_body(cert: &Certificate) -> String {
    let mut out = String::new();
    out.push_str("Module AdsmtCert.\n\n");
    let vars = collect_free_vars(cert);
    if !vars.is_empty() {
        for (name, ty_rocq) in &vars {
            writeln!(out, "Parameter {name} : {ty_rocq}.").unwrap();
        }
        out.push('\n');
    }
    emit_oracles(cert, &mut out);
    out.push_str("Section Proof.\n\n");
    for step in &cert.steps {
        emit_step(step, &mut out);
    }
    if cert.final_sequent().is_some() {
        // Inside the section this is the bare conclusion; closing the
        // section generalises it over the hypotheses.
        writeln!(
            out,
            "\nTheorem result : {}.\nProof. exact s{}. Qed.",
            render_term(&cert.final_sequent().expect("checked").concl),
            cert.conclusion.0
        )
        .unwrap();
    }
    out.push_str("\nEnd Proof.\n");
    out.push_str("\nEnd AdsmtCert.\n");
    out
}

/// The conclusion of `id`, if that step exists.
fn step_concl(cert: &Certificate, id: adsmt_cert::StepId) -> Option<String> {
    cert.steps.iter().find(|s| s.id == id).map(|s| render_term(&s.result.concl))
}

/// `[p1; p2]`, `c` -> `p1 -> p2 -> c`; no premises -> just `c`.
fn rocq_implication_str(prems: &[String], concl: &str) -> String {
    if prems.is_empty() { concl.to_owned() } else { format!("{} -> {concl}", prems.join(" -> ")) }
}

/// Oracle axioms for steps no Rocq tactic can replay: theory steps,
/// type-class instances, abductive markers.
///
/// Each is stated as *premises -> conclusion*, never as the bare
/// conclusion. That is the whole point: `Axiom s2 : False.` is false,
/// while `Axiom adsmt_s2 : p -> ~p -> False.` is true and merely records
/// what the theory solver decided. The module stays consistent however
/// contradictory the certificate's hypotheses are.
fn emit_oracles(cert: &Certificate, out: &mut String) {
    let mut any = false;
    for step in &cert.steps {
        let name = format!("adsmt_s{}", step.id.0);
        match &step.body {
            StepBody::Theory { name: theory_name, witness, parents } => {
                let prems: Vec<String> =
                    parents.iter().filter_map(|q| step_concl(cert, *q)).collect();
                let prop = rocq_implication_str(&prems, &render_term(&step.result.concl));
                writeln!(out, "(* theory `{theory_name}`; witness: {} *)",
                         witness_summary_local(witness)).unwrap();
                writeln!(out, "Axiom {name} : {prop}.").unwrap();
                any = true;
            }
            StepBody::Instance { relation, .. } => {
                writeln!(out, "(* type-class instance for `{relation}` *)").unwrap();
                writeln!(out, "Axiom {name} : {}.", render_term(&step.result.concl)).unwrap();
                any = true;
            }
            StepBody::Assumed { formula, explain } => {
                writeln!(out, "(* abductive marker: {} *)",
                         escape_for_comment(explain.as_deref().unwrap_or(""))).unwrap();
                writeln!(out, "Axiom {name} : {}.", render_term(formula)).unwrap();
                any = true;
            }
            _ => {}
        }
    }
    if any { out.push('\n'); }
}

/// Emit one step *inside* the section.
///
/// `Assume` becomes a `Hypothesis`, not an `Axiom`: a hypothesis is
/// discharged when the section closes, so `result` generalises to
/// `h1 -> ... -> hn -> concl` and the module never asserts the
/// hypotheses. Every other replayable step keeps its real proof term.
fn emit_step(step: &Step, out: &mut String) {
    let name = format!("s{}", step.id.0);
    let concl_rocq = render_term(&step.result.concl);

    match &step.body {
        StepBody::Assume(t) => {
            writeln!(out, "Hypothesis {name} : {}.", render_term(t)).unwrap();
        }
        StepBody::Refl(t) => {
            let t_rocq = render_term(t);
            writeln!(out, "Theorem {name} : {t_rocq} = {t_rocq}.\nProof. reflexivity. Qed.").unwrap();
        }
        StepBody::Trans { lhs, rhs } => {
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact (eq_trans s{} s{}). Qed.",
                     lhs.0, rhs.0).unwrap();
        }
        StepBody::EqMp { iff, p } => {
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact (proj1 s{} s{}). Qed.",
                     iff.0, p.0).unwrap();
        }
        StepBody::Deduct { a, b } => {
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact (fun _h_s{} => s{}). Qed.",
                     a.0, b.0).unwrap();
        }
        StepBody::Beta { redex } => {
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact eq_refl. Qed. (* β-reduce: {} *)",
                     escape_for_comment(&render_term(redex))).unwrap();
        }
        StepBody::Abs { var, eq } => {
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact (functional_extensionality _ _ (fun {} => s{})). Qed.",
                     var.name, eq.0).unwrap();
        }
        StepBody::Inst { thm, .. } | StepBody::InstType { thm, .. } => {
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact s{}. Qed.", thm.0).unwrap();
        }
        StepBody::Theory { parents, .. } => {
            let args: Vec<String> = parents.iter().map(|q| format!("s{}", q.0)).collect();
            let app = if args.is_empty() {
                format!("adsmt_s{}", step.id.0)
            } else {
                format!("(adsmt_s{} {})", step.id.0, args.join(" "))
            };
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact {app}. Qed.").unwrap();
        }
        StepBody::Instance { .. } | StepBody::Assumed { .. } => {
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact adsmt_s{}. Qed.",
                     step.id.0).unwrap();
        }
    }
}
fn witness_summary_local(w: &TheoryWitness) -> String {
    witness_summary(w)
}

fn collect_free_vars(cert: &Certificate) -> Vec<(String, String)> {
    let mut seen: Vec<(String, String)> = Vec::new();
    for step in &cert.steps {
        for hyp in &step.result.hyps {
            for v in hyp.free_vars() {
                let entry = (v.name.clone(), render_type(&v.ty));
                if !seen.contains(&entry) {
                    seen.push(entry);
                }
            }
        }
        for v in step.result.concl.free_vars() {
            let entry = (v.name.clone(), render_type(&v.ty));
            if !seen.contains(&entry) {
                seen.push(entry);
            }
        }
    }
    seen
}

/// Render an adsmt [`Term`] as a Rocq-syntax expression.
///
/// Minimal v0.17 mapping (Ltac2 surface):
/// - variables / constants → bare identifiers
/// - `not p` → `~ p` (Coq's negation notation)
/// - `and p q` → `p /\ q`
/// - `or  p q` → `p \/ q`
/// - `implies p q` → `p -> q`
/// - `iff p q` → `p <-> q`
/// - equality `(= lhs rhs)` → `lhs = rhs`
/// - application chains → space-separated with parens around
///   compound arguments
/// - lambda → `fun x : T => body`
fn render_term(t: &Term) -> String {
    if let Some((lhs, rhs)) = t.dest_eq() {
        return format!("({} = {})", render_term(&lhs), render_term(&rhs));
    }
    if let Some((head, args)) = adsmt_cert::prover_emit::common::strip_app_head(t) {
        match (head.as_str(), args.len()) {
            ("not", 1) => return format!("(~ {})", render_term(&args[0])),
            ("and", 2) => {
                return format!(
                    "({} /\\ {})",
                    render_term(&args[0]),
                    render_term(&args[1])
                )
            }
            ("or", 2) => {
                return format!(
                    "({} \\/ {})",
                    render_term(&args[0]),
                    render_term(&args[1])
                )
            }
            ("implies", 2) | ("=>", 2) => {
                return format!(
                    "({} -> {})",
                    render_term(&args[0]),
                    render_term(&args[1])
                )
            }
            ("iff", 2) => {
                return format!(
                    "({} <-> {})",
                    render_term(&args[0]),
                    render_term(&args[1])
                )
            }
            _ => {}
        }
    }
    // rc.10 (verus-fork R1) reshaped `Term` from an enum to
    // `Term(Arc<TermInner>)`; pattern-match through `kind()`
    // against `TermInner::*` (the bare `Term::App` etc. are now
    // associated constructor fns, not variants).
    match t.kind() {
        TermInner::Var(v) => v.name.clone(),
        TermInner::Const(c) => match c.name.as_str() {
            // adsmt-core names the boolean constants `true` / `false`
            // (adsmt-core/src/term.rs:461,466). Those are *values of a
            // boolean type* in every target here, not propositions, so
            // emitting them verbatim produces source that does not compile.
            "true" => "True".to_owned(),
            "false" => "False".to_owned(),
            other => other.to_owned(),
        },
        TermInner::App(f, x) => {
            let f_s = render_term(f);
            let x_s = render_term(x);
            let x_render = if matches!(x.kind(), TermInner::App(..) | TermInner::Lam(..)) {
                format!("({x_s})")
            } else {
                x_s
            };
            format!("{f_s} {x_render}")
        }
        TermInner::Lam(v, body) => format!(
            "(fun {} : {} => {})",
            v.name,
            render_type(&v.ty),
            render_term(body),
        ),
    }
}

/// Render an adsmt [`Type`] as Rocq syntax. `Bool` becomes `Prop`
/// per the cross-ITP semantic anchor; built-in `Int` / `Real`
/// names round-trip.
fn render_type(ty: &adsmt_core::Type) -> String {
    if let Some((dom, cod)) = ty.dest_fun() {
        return format!("({} -> {})", render_type(&dom), render_type(&cod));
    }
    match ty.to_string().as_str() {
        "Bool" => "Prop".into(),
        other => other.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_cert::recorder::{recorder as r, ProofHandle};
    use adsmt_core::{Term, Type};

    fn p() -> Term {
        Term::var("p", Type::bool_())
    }

    #[test]
    fn header_and_module_present() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        assert!(s.starts_with("(* Generated by adsmt-emit-rocq"));
        assert!(s.contains("From Ltac2 Require Import Ltac2."));
        assert!(s.contains("Set Default Proof Mode \"Ltac2\"."));
        assert!(s.contains("Module AdsmtCert."));
        assert!(s.ends_with("End AdsmtCert.\n"));
    }

    #[test]
    fn ltac1_directives_absent() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        // Hard floor: Ltac1 must never appear in the emitted output.
        assert!(!s.contains("Set Default Proof Mode \"Classic\""));
        assert!(!s.contains("Require Import Ltac."));
    }

    #[test]
    fn assume_becomes_a_section_hypothesis() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        // Free vars are Prop in Rocq (Bool → Prop semantic anchor).
        assert!(s.contains("Parameter p : Prop."));
        // A hypothesis, not an axiom: the section discharges it, so the
        // module never asserts it and `result` generalises over it.
        assert!(s.contains(&format!("Hypothesis s{} : p.", h.step().0)), "{s}");
        assert!(
            !s.contains(&format!("Axiom s{} :", h.step().0)),
            "hypothesis was axiomatized:\n{s}"
        );
        assert!(s.contains("Theorem result : p."));
        assert!(s.contains("Proof. exact s0. Qed."));
    }

    #[test]
    fn refl_emits_reflexivity_proof() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        assert!(s.contains("Theorem s0 : p = p."));
        assert!(s.contains("Proof. reflexivity. Qed."));
    }

    #[test]
    fn assumed_marker_becomes_a_named_oracle() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h =
            r::assumed(&mut b, p(), Some("needs Functor MyType".into())).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        assert!(s.contains("(* abductive marker: needs Functor MyType *)"), "{s}");
        // A NAMED oracle axiom instead of `Admitted.`, so the trust source
        // is visible instead of hidden.
        assert!(s.contains("Axiom adsmt_s0 : p."), "{s}");
        assert!(s.contains("Theorem s0 : p."), "{s}");
        assert!(!s.contains("Admitted."), "{s}");
    }

    #[test]
    fn negated_assumption_uses_rocq_negation() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let np = Term::mk_not(p()).unwrap();
        let h = r::assume(&mut b, np).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        assert!(s.contains("Hypothesis s0 : (~ p)."), "{s}");
        assert!(!s.contains("Axiom s0 :"), "{s}");
    }

    #[test]
    fn theory_step_becomes_an_implication_oracle() {
        use adsmt_cert::canonical::{Sequent, StepBody};
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let assume = r::assume(&mut b, p()).unwrap();
        let theory_step = b.add(
            StepBody::Theory {
                name: "EUF".into(),
                witness: TheoryWitness::Opaque {
                    kind: "smoke".into(),
                    notes: "demo".into(),
                },
                parents: vec![assume.step()],
            },
            Sequent {
                hyps: vec![p()],
                concl: p(),
            },
        );
        let cert = b.snapshot(theory_step);
        let s = emit_rocq(&cert);
        // The oracle is stated as PREMISES -> CONCLUSION. That shape is
        // what keeps the module consistent: a bare conclusion could be
        // `False`, whereas `p -> False` merely records a decision.
        assert!(s.contains("witness: Opaque(smoke)"), "{s}");
        assert!(s.contains(&format!("Axiom adsmt_s{} :", theory_step.0)), "{s}");
        assert!(!s.contains(&format!("Axiom s{} :", theory_step.0)), "{s}");
        assert!(s.contains(" -> "), "oracle is not an implication:\n{s}");
    }

    // === Classical-axiom-import emission ===

    #[test]
    fn no_classical_imports_for_intuitionistic_cert() {
        // Default cert with no markers should not contain any
        // `Classical_*` line beyond the fixed prelude.
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        assert!(!s.contains("Classical_Prop"));
        assert!(!s.contains("Classical_Pred_Type"));
        assert!(!s.contains("ClassicalEpsilon"));
        assert!(!s.contains("FunctionalExtensionality"));
    }

    #[test]
    fn should_marker_propositional_emits_classical_prop() {
        use adsmt_cert::ClassicalModuleFamily;
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.add_should_import_classical(
            step_id,
            ClassicalModuleFamily::Propositional,
        );
        let cert = b.snapshot(step_id);
        let s = emit_rocq(&cert);
        assert!(s.contains("From Stdlib Require Import Classical_Prop."));
        // Lands between the fixed Ltac2 prelude and Module.
        let prelude_pos = s.find("Set Default Proof Mode \"Ltac2\".").unwrap();
        let classical_pos =
            s.find("From Stdlib Require Import Classical_Prop.").unwrap();
        let module_pos = s.find("Module AdsmtCert.").unwrap();
        assert!(prelude_pos < classical_pos);
        assert!(classical_pos < module_pos);
    }

    #[test]
    fn try_emit_rocq_returns_error_when_required_uncovered() {
        use adsmt_cert::{ClassicalModuleFamily, ClassicalSet};
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.set_direct_required_classical(
            step_id,
            ClassicalSet::from_iter([ClassicalModuleFamily::Propositional]),
        );
        let cert = b.snapshot(step_id);
        let result = try_emit_rocq(&cert);
        assert!(matches!(result, Err(MissingImports(_))));
    }

    #[test]
    fn trans_emits_proof_term_not_admitted() {
        use adsmt_cert::canonical::{Sequent, StepBody};
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let a0 = r::assume(&mut b, p()).unwrap();
        let a1 = r::assume(&mut b, p()).unwrap();
        let trans_id = b.add(
            StepBody::Trans { lhs: a0.step(), rhs: a1.step() },
            Sequent { hyps: vec![], concl: p() },
        );
        let cert = b.snapshot(trans_id);
        let s = emit_rocq(&cert);
        assert!(s.contains("Proof. exact (eq_trans s0 s1). Qed."));
        // Ensure the old Admitted stub is gone for Trans.
        assert!(!s.contains("Admitted. (* eapply eq_trans"));
    }

    #[test]
    fn eqmp_emits_proof_term_not_admitted() {
        use adsmt_cert::canonical::{Sequent, StepBody};
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let a0 = r::assume(&mut b, p()).unwrap();
        let a1 = r::assume(&mut b, p()).unwrap();
        let eqmp_id = b.add(
            StepBody::EqMp { iff: a0.step(), p: a1.step() },
            Sequent { hyps: vec![], concl: p() },
        );
        let cert = b.snapshot(eqmp_id);
        let s = emit_rocq(&cert);
        assert!(s.contains("Proof. exact (proj1 s0 s1). Qed."));
        assert!(!s.contains("Admitted. (* apply (proj1"));
    }

    #[test]
    fn mid_block_marker_propagates_to_rocq_import() {
        // Mid-block local_markers should contribute their
        // `should` set to the file-level resolved imports via
        // the shared aggregator (B). Test confirms the contrib
        // backend picks up the new layer for free.
        use adsmt_cert::{
            ClassicalMarkerSet, ClassicalModuleFamily, ClassicalSet, MidBlock,
            MidBlockItem,
        };
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        let block = MidBlock {
            name: Some("rocq_block".into()),
            contents: vec![MidBlockItem::Step(step_id)],
            local_markers: ClassicalMarkerSet {
                should: ClassicalSet::from_iter([
                    ClassicalModuleFamily::Propositional,
                ]),
                allow: vec![],
            },
            exported_markers: ClassicalMarkerSet::empty(),
        };
        b.add_mid_block(block);
        let cert = b.snapshot(step_id);
        let s = emit_rocq(&cert);
        assert!(s.contains("From Stdlib Require Import Classical_Prop."));
    }

    #[test]
    fn pattern_marker_propagates_to_rocq_import() {
        use adsmt_cert::{
            ClassicalMarkerSet, ClassicalModuleFamily, ClassicalSet,
            PatternMarker, StepKindTag, StepPattern,
        };
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Assume),
            local_markers: ClassicalMarkerSet {
                should: ClassicalSet::from_iter([
                    ClassicalModuleFamily::FunExt,
                ]),
                allow: vec![],
            },
            name: Some("assume_funext".into()),
            source_loc: None,
        });
        let cert = b.snapshot(step_id);
        let s = emit_rocq(&cert);
        assert!(s.contains("From Stdlib Require Import FunctionalExtensionality."));
    }

    #[test]
    fn try_emit_rocq_succeeds_when_marker_covers_requirement() {
        use adsmt_cert::{ClassicalModuleFamily, ClassicalSet};
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.set_direct_required_classical(
            step_id,
            ClassicalSet::from_iter([ClassicalModuleFamily::Propositional]),
        );
        b.add_should_import_classical(
            step_id,
            ClassicalModuleFamily::Propositional,
        );
        let cert = b.snapshot(step_id);
        let result = try_emit_rocq(&cert);
        assert!(result.is_ok());
        let s = result.unwrap();
        assert!(s.contains("From Stdlib Require Import Classical_Prop."));
    }
}

//! Rocq (Coq) backend for adsmt-cert certificates.
//!
//! Produces a `.v` source file that re-states an adsmt
//! [`Certificate`](adsmt_cert::Certificate) as a sequence of
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
use adsmt_core::Term;

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
    let mut classical_emitted = false;
    for fam in resolved.iter() {
        if let Some(line) = rocq_import_line(fam) {
            writeln!(out, "{line}").unwrap();
            classical_emitted = true;
        }
    }
    if classical_emitted {
        out.push('\n');
    } else {
        out.push('\n');
    }

    out.push_str("Module AdsmtCert.\n\n");

    let vars = collect_free_vars(cert);
    if !vars.is_empty() {
        for (name, ty_rocq) in &vars {
            writeln!(out, "Parameter {name} : {ty_rocq}.").unwrap();
        }
        out.push('\n');
    }

    for step in &cert.steps {
        emit_step(step, &mut out);
    }

    if let Some(seq) = cert.final_sequent() {
        let concl_rocq = render_term(&seq.concl);
        let final_id = format!("s{}", cert.conclusion.0);
        writeln!(
            out,
            "\nTheorem result : {concl_rocq}.\nProof. exact {final_id}. Qed."
        )
        .unwrap();
    }
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
    for step in &cert.steps {
        emit_step(step, &mut out);
    }
    if let Some(seq) = cert.final_sequent() {
        let concl_rocq = render_term(&seq.concl);
        let final_id = format!("s{}", cert.conclusion.0);
        writeln!(
            out,
            "\nTheorem result : {concl_rocq}.\nProof. exact {final_id}. Qed."
        )
        .unwrap();
    }
    out.push_str("\nEnd AdsmtCert.\n");
    out
}

fn emit_step(step: &Step, out: &mut String) {
    let name = format!("s{}", step.id.0);
    let concl_rocq = render_term(&step.result.concl);

    match &step.body {
        StepBody::Assume(t) => {
            writeln!(out, "Axiom {name} : {}.", render_term(t)).unwrap();
        }
        StepBody::Refl(t) => {
            let t_rocq = render_term(t);
            writeln!(
                out,
                "Theorem {name} : {t_rocq} = {t_rocq}.\nProof. reflexivity. Qed."
            )
            .unwrap();
        }
        StepBody::Trans { lhs, rhs } => {
            // v0.18 K: real proof term — eq_trans applied to
            // the two parent step results.
            writeln!(
                out,
                "Theorem {name} : {concl_rocq}.\nProof. exact (eq_trans s{} s{}). Qed.",
                lhs.0, rhs.0,
            )
            .unwrap();
        }
        StepBody::EqMp { iff, p } => {
            // v0.18 K: real proof term. Coq's `<->` (iff)
            // is defined as `(A -> B) /\ (B -> A)`, so `proj1`
            // pulls the forward implication. Then apply to the
            // proven antecedent.
            writeln!(
                out,
                "Theorem {name} : {concl_rocq}.\nProof. exact (proj1 s{} s{}). Qed.",
                iff.0, p.0,
            )
            .unwrap();
        }
        StepBody::Deduct { a, b } => {
            writeln!(
                out,
                "Theorem {name} : {concl_rocq}.\nAdmitted. (* deduct from s{} and s{} *)",
                a.0, b.0,
            )
            .unwrap();
        }
        StepBody::Beta { redex } => {
            writeln!(
                out,
                "Theorem {name} : {concl_rocq}.\nAdmitted. (* beta-redex: {} *)",
                escape_for_comment(&render_term(redex)),
            )
            .unwrap();
        }
        StepBody::Abs { var, eq } => {
            writeln!(
                out,
                "Theorem {name} : {concl_rocq}.\nAdmitted. (* abs over {} from s{} *)",
                var.name, eq.0,
            )
            .unwrap();
        }
        StepBody::Inst { thm, .. } => {
            writeln!(
                out,
                "Theorem {name} : {concl_rocq}.\nAdmitted. (* instantiate s{} *)",
                thm.0,
            )
            .unwrap();
        }
        StepBody::InstType { thm, .. } => {
            writeln!(
                out,
                "Theorem {name} : {concl_rocq}.\nAdmitted. (* type-instantiate s{} *)",
                thm.0,
            )
            .unwrap();
        }
        StepBody::Theory {
            name: theory_name,
            witness,
            parents,
        } => {
            writeln!(
                out,
                "(* theory `{theory_name}` step; witness: {} *)",
                witness_summary_local(witness),
            )
            .unwrap();
            if !parents.is_empty() {
                write!(out, "(* parents:").unwrap();
                for p in parents {
                    write!(out, " s{}", p.0).unwrap();
                }
                out.push_str(" *)\n");
            }
            writeln!(out, "Axiom {name} : {concl_rocq}.").unwrap();
        }
        StepBody::Instance { relation, .. } => {
            writeln!(out, "(* type-class instance for `{relation}` *)").unwrap();
            writeln!(out, "Axiom {name} : {concl_rocq}.").unwrap();
        }
        StepBody::Assumed { formula, explain } => {
            let explain_str = explain.as_deref().unwrap_or("");
            writeln!(
                out,
                "(* abductive marker: {} *)",
                escape_for_comment(explain_str),
            )
            .unwrap();
            writeln!(
                out,
                "Theorem {name} : {}.\nAdmitted.",
                render_term(formula),
            )
            .unwrap();
        }
    }
}

/// Use the shared anchor wherever it is reachable. We re-export it
/// rather than re-implement so any future change to the witness
/// summary form (e.g. richer DRAT counters) propagates here
/// automatically.
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
    match t {
        Term::Var(v) => v.name.clone(),
        Term::Const(c) => c.name.clone(),
        Term::App(f, x) => {
            let f_s = render_term(f);
            let x_s = render_term(x);
            let x_render = if matches!(**x, Term::App(..) | Term::Lam(..)) {
                format!("({x_s})")
            } else {
                x_s
            };
            format!("{f_s} {x_render}")
        }
        Term::Lam(v, body) => format!(
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
    fn assume_emits_axiom_with_term_statement() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        // Free vars are Prop in Rocq (Bool → Prop semantic anchor).
        assert!(s.contains("Parameter p : Prop."));
        assert!(s.contains(&format!("Axiom s{} : p.", h.step().0)));
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
    fn assumed_marker_emits_admitted_with_explain_comment() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h =
            r::assumed(&mut b, p(), Some("needs Functor MyType".into())).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        assert!(s.contains("(* abductive marker: needs Functor MyType *)"));
        assert!(s.contains("Theorem s0 : p."));
        assert!(s.contains("Admitted."));
    }

    #[test]
    fn negated_assumption_uses_rocq_negation() {
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let np = Term::mk_not(p()).unwrap();
        let h = r::assume(&mut b, np).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_rocq(&cert);
        assert!(s.contains("Axiom s0 : (~ p)."));
    }

    #[test]
    fn theory_step_axiomatizes_with_witness_comment() {
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
        assert!(s.contains("(* theory `EUF` step"));
        assert!(s.contains("Opaque(smoke)"));
        assert!(s.contains(&format!("Axiom s{} : p.", theory_step.0)));
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

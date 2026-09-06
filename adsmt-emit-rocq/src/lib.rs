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

use std::collections::BTreeSet;
use std::fmt::Write;

use adsmt_cert::sexpr_render;
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
    // Target-logic binding, stated per backend rather than copied from the
    // Isabelle one: this output is Rocq/Coq's Prop with Stdlib.Logic and
    // Ltac2, not Isabelle/HOL and not Lean.
    out.push_str("(* Target logic: Rocq/Coq `Prop` with Stdlib.Logic + Ltac2. *)\n");
    out.push_str("(* Build declaration - write this next to the file as `_CoqProject`:\n");
    for line in emit_rocq_project().lines() {
        out.push_str("     ");
        out.push_str(line);
        out.push('\n');
    }
    out.push_str("*)\n");
    out.push_str("From Stdlib Require Import Logic.\n");
    let (need_z, need_r) = numeric_imports(cert);
    if need_z {
        out.push_str("From Stdlib Require Import ZArith.\n");
    }
    if need_r {
        out.push_str("From Stdlib Require Import Reals.\n");
    }
    for req in cert.signature.required_imports("rocq") {
        writeln!(out, "Require Import {req}.").unwrap();
    }
    out.push_str("From Ltac2 Require Import Ltac2.\n");
    out.push_str("Set Default Proof Mode \"Ltac2\".\n");
    if need_z {
        out.push_str("Open Scope Z_scope.\n");
    }

    // Classical-axiom imports (between fixed prelude and Module).
    // The trailing blank line separates this block from the
    // Module wrapper regardless of whether any imports landed.
    for fam in resolved.iter() {
        if let Some(line) = rocq_import_line(fam) {
            writeln!(out, "{line}").unwrap();
        }
    }
    out.push('\n');

    for sym in unmapped_constants(cert) {
        writeln!(
            out,
            "(* UNMAPPED SYMBOL: `{sym}` is emitted verbatim and may not \
parse in Rocq. *)"
        )
        .unwrap();
    }
    for line in adsmt_cert::recheck::trust_summary(cert, "").lines() {
        writeln!(out, "(* {line} *)").unwrap();
    }
    out.push('\n');
    out.push_str("Module AdsmtCert.\n\n");

    let declared = emit_declarations(cert, &mut out);
    let vars: Vec<_> = collect_free_vars(cert)
        .into_iter()
        .filter(|(n, _)| !declared.contains(n))
        .collect();
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
    // Rocq's equivalent of `Thm_Deps.all_oracles`: it lists exactly the
    // axioms `result` leans on, so the trust surface is countable from the
    // artifact instead of having to be taken on faith.
    out.push_str(
        "\n(* Trust surface: the `adsmt_s*` oracles, plus the axioms the\n\
   DECLARATION context introduces (uninterpreted sorts/functions and\n\
   datatype selectors). Nothing else may appear. *)\n",
    );
    out.push_str("Print Assumptions AdsmtCert.result.\n");
    Ok(out)
}

/// Render the cert body **without** any classical-axiom prelude
/// or the fixed Ltac2 prelude. Used by [`try_emit_rocq`]'s
/// pass-1 preliminary render for the D1.B
/// `lazy=true, scan=true` text-scan arm.
fn render_body(cert: &Certificate) -> String {
    let mut out = String::new();
    for sym in unmapped_constants(cert) {
        writeln!(
            out,
            "(* UNMAPPED SYMBOL: `{sym}` is emitted verbatim and may not \
parse in Rocq. *)"
        )
        .unwrap();
    }
    for line in adsmt_cert::recheck::trust_summary(cert, "").lines() {
        writeln!(out, "(* {line} *)").unwrap();
    }
    out.push('\n');
    out.push_str("Module AdsmtCert.\n\n");
    let declared = emit_declarations(cert, &mut out);
    let vars: Vec<_> = collect_free_vars(cert)
        .into_iter()
        .filter(|(n, _)| !declared.contains(n))
        .collect();
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

/// The oracle axiom's name for a step.
///
/// A USER-SUPPLIED assumption gets a visibly different name from a
/// theory decision, because `Print Assumptions` lists axioms by name:
/// were both `adsmt_s<i>`, a reader could not tell "the SAT solver
/// decided this" from "the user asked us to assume this" (constraint
/// (3)(C) rule 1).
fn oracle_name(step: &Step) -> String {
    match &step.body {
        StepBody::Assumed { .. } => format!("adsmt_assumed_s{}", step.id.0),
        _ => format!("adsmt_s{}", step.id.0),
    }
}

fn emit_oracles(cert: &Certificate, out: &mut String) {
    let mut any = false;
    for step in &cert.steps {
        let name = oracle_name(step);
        match &step.body {
            StepBody::Theory { name: theory_name, witness, parents } => {
                let prems: Vec<String> =
                    parents.iter().filter_map(|q| step_concl(cert, *q)).collect();
                let prop = rocq_implication_str(&prems, &render_term(&step.result.concl));
                writeln!(out, "(* theory `{theory_name}`; witness: {} *)",
                         witness_summary_local(witness)).unwrap();
                // Constraint (3)(B): a user tactic REPLACES the oracle.
                // Fail-first — Rocq still checks it, so a tactic that
                // does not close the goal breaks the build rather than
                // being believed. On success the step stops being a
                // trust source at all.
                match cert.signature.tactic_for(step.id, Some(theory_name), "rocq") {
                    Some(tac) => {
                        writeln!(out, "(* user tactic hint (replaces the oracle) *)").unwrap();
                        writeln!(out, "Theorem {name} : {prop}.\nProof. {tac} Qed.").unwrap();
                    }
                    None => writeln!(out, "Axiom {name} : {prop}.").unwrap(),
                }
                any = true;
            }
            StepBody::Instance { relation, .. } => {
                writeln!(out, "(* type-class instance for `{relation}` *)").unwrap();
                writeln!(out, "Axiom {name} : {}.", render_term(&step.result.concl)).unwrap();
                any = true;
            }
            StepBody::Assumed { formula, explain } => {
                writeln!(out, "(* USER-SUPPLIED ASSUMPTION (not proved): {} *)",
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
        StepBody::MkComb { fun_eq, arg_eq } => {
            // `f_equal2 (fun f x => f x)` states this rule in Rocq:
            // from `f = g` and `x = y`, `f x = g y`. A real proof term,
            // not an oracle.
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact (f_equal2 (fun f x => f x) s{} s{}). Qed.",
                     fun_eq.0, arg_eq.0).unwrap();
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
            writeln!(out, "Theorem {name} : {concl_rocq}.\nProof. exact {}. Qed.",
                     oracle_name(step)).unwrap();
        }
    }
}
fn witness_summary_local(w: &TheoryWitness) -> String {
    witness_summary(w)
}


/// Emit the certificate's declaration context — sorts, datatypes,
/// function signatures — and return every name it declared.
///
/// Constraint (1) rule 1: before this, declarations were reconstructed
/// by scanning free variables, which cannot recover a sort no term
/// mentions, a constructor's arity, a selector name, or the
/// `declare-fun` vs `define-fun` distinction.
fn emit_declarations(cert: &Certificate, out: &mut String) -> BTreeSet<String> {
    let sig = &cert.signature;
    // Constraint (3)(A): a user mapping says what a name MEANS in the
    // target — meaning the emitter cannot infer, and checkable, since
    // the emitted theory either typechecks or it does not.
    let render_sort_name = |s: &str| {
        let mapped = sig.mapped_name(s, "rocq");
        if mapped == s { render_sort_name(s) } else { mapped.to_owned() }
    };
    let mut declared = BTreeSet::new();
    if sig.is_empty() {
        return declared;
    }

    // Uninterpreted sorts. `Parameter S : Type` does NOT make `S`
    // inhabited in Rocq, whereas an SMT-LIB sort is non-empty by
    // definition — hence the companion axiom, without which the
    // translation would be strictly weaker than the input.
    let user_sorts: Vec<_> = sig
        .sorts
        .iter()
        .filter(|s| {
            // A MAPPED sort already exists in the target, so
            // re-declaring it would shadow the real one.
            !s.builtin
                && !sig.datatypes.iter().any(|d| d.sort_name == s.name)
                && sig.mapped_name(&s.name, "rocq") == s.name
        })
        .collect();
    if !user_sorts.is_empty() {
        out.push_str("(* Uninterpreted sorts (non-empty, per SMT-LIB) *)\n");
        for s in &user_sorts {
            let arrows = "Type -> ".repeat(s.arity as usize);
            writeln!(out, "Parameter {} : {arrows}Type.", s.name).unwrap();
            if s.arity == 0 {
                writeln!(out, "Axiom {}_nonempty : inhabited {}.", s.name, s.name).unwrap();
            }
            declared.insert(s.name.clone());
        }
        out.push('\n');
    }

    // Datatypes become real `Inductive` declarations, so constructor
    // injectivity and distinctness come from the kernel rather than
    // being asserted — no trust cost.
    for d in &sig.datatypes {
        let params: String =
            d.params.iter().map(|p| format!(" ({p} : Type)")).collect();
        writeln!(out, "Inductive {}{params} : Type :=", d.sort_name).unwrap();
        for (i, ctor) in d.constructors.iter().enumerate() {
            let arity = d.arities.get(i).copied().unwrap_or(0) as usize;
            match d.field_sorts.get(i) {
                Some(fs) if fs.len() == arity => {
                    let mut ty = String::new();
                    for f in fs {
                        write!(ty, "{} -> ", render_sort_name(f)).unwrap();
                    }
                    writeln!(out, "  | {ctor} : {ty}{}", d.sort_name).unwrap();
                }
                _ if arity == 0 => {
                    writeln!(out, "  | {ctor} : {}", d.sort_name).unwrap();
                }
                // Arity without field sorts: guessing the types would be
                // the silent mistranslation rule (1)(2) forbids.
                _ => {
                    writeln!(
                        out,
                        "  (* INCOMPLETE: `{ctor}` takes {arity} argument(s) whose sorts \
the certificate did not carry *)"
                    )
                    .unwrap();
                    writeln!(out, "  | {ctor} : {}", d.sort_name).unwrap();
                }
            }
            declared.insert(ctor.clone());
        }
        out.push_str(".\n");
        declared.insert(d.sort_name.clone());

        // Selectors are partial in SMT-LIB (`hd nil` is unconstrained),
        // so they are axioms with a characteristic equation rather than
        // total definitions — which is what the input actually said.
        for (i, sels) in d.selectors.iter().enumerate() {
            let Some(ctor) = d.constructors.get(i) else { continue };
            let Some(fs) = d.field_sorts.get(i) else { continue };
            if fs.len() != sels.len() {
                continue;
            }
            for (j, sel) in sels.iter().enumerate() {
                writeln!(
                    out,
                    "Parameter {sel} : {} -> {}.",
                    d.sort_name,
                    render_sort_name(&fs[j])
                )
                .unwrap();
                let binders: String = fs
                    .iter()
                    .enumerate()
                    .map(|(k, f)| format!(" (x{k} : {})", render_sort_name(f)))
                    .collect();
                let args: String = (0..fs.len()).map(|k| format!(" x{k}")).collect();
                writeln!(
                    out,
                    "Axiom {sel}_{ctor} : forall{binders}, {sel} ({ctor}{args}) = x{j}."
                )
                .unwrap();
                declared.insert(sel.clone());
            }
        }
        out.push('\n');
    }

    // Functions and constants. A `define-fun` keeps its definition — a
    // `Definition`, not a `Parameter` — so the defining equation stays
    // available to `simpl`/`reflexivity`.
    if !sig.funs.is_empty() {
        for f in &sig.funs {
            if sig.mapped_name(&f.name, "rocq") != f.name {
                // Mapped to something the target already provides.
                declared.insert(f.name.clone());
                continue;
            }
            let ty = fun_type_in(sig, &f.params, &f.result);
            match &f.body {
                Some(body) => {
                    let mut unmapped = BTreeSet::new();
                    match sexpr_render::parse(body) {
                        Some(sx) => {
                            let rendered =
                                sexpr_render::render(&sx, &sexpr_render::ROCQ, &mut unmapped);
                            for u in &unmapped {
                                writeln!(out, "(* UNMAPPED OPERATOR in `{}`: `{u}` *)", f.name)
                                    .unwrap();
                            }
                            let binders: String = f
                                .param_names
                                .iter()
                                .zip(&f.params)
                                .map(|(n, s)| format!(" ({n} : {})", render_sort_name(s)))
                                .collect();
                            writeln!(
                                out,
                                "Definition {}{binders} : {} := {rendered}.",
                                f.name,
                                render_sort_name(&f.result)
                            )
                            .unwrap();
                        }
                        None => {
                            writeln!(
                                out,
                                "(* UNPARSEABLE define-fun body for `{}`; emitted as \
uninterpreted *)",
                                f.name
                            )
                            .unwrap();
                            writeln!(out, "Parameter {} : {ty}.", f.name).unwrap();
                        }
                    }
                }
                None => writeln!(out, "Parameter {} : {ty}.", f.name).unwrap(),
            }
            declared.insert(f.name.clone());
        }
        out.push('\n');
    }
    declared
}

/// `["Int", "Int"]`, `"Bool"` -> `Z -> Z -> Prop`.
fn fun_type_in(
    sig: &adsmt_cert::canonical::Signature,
    params: &[String],
    result: &str,
) -> String {
    let m = |s: &str| {
        let mapped = sig.mapped_name(s, "rocq");
        if mapped == s { render_sort_name(s) } else { mapped.to_owned() }
    };
    let mut ty = String::new();
    for p in params {
        write!(ty, "{} -> ", m(p)).unwrap();
    }
    ty.push_str(&m(result));
    ty
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
            ("<", 2) => {
                return format!("({} < {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("<=", 2) => {
                return format!("({} <= {})", render_term(&args[0]), render_term(&args[1]))
            }
            (">", 2) => {
                return format!("({} > {})", render_term(&args[0]), render_term(&args[1]))
            }
            (">=", 2) => {
                return format!("({} >= {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("+", 2) => {
                return format!("({} + {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("-", 2) => {
                return format!("({} - {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("*", 2) => {
                return format!("({} * {})", render_term(&args[0]), render_term(&args[1]))
            }
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
    use adsmt_core::Type as T;
    if let Some((dom, cod)) = ty.dest_fun() {
        return format!("({} -> {})", render_type(&dom), render_type(&cod));
    }
    // A higher-kinded application (`Seq Int`) must be taken apart: sent
    // through `to_string()` it would carry the SMT-LIB spelling of its
    // argument into Rocq, which has no `Int`. Rocq's type application is
    // prefix, like the source.
    if let T::App(f, a) = ty {
        let arg = render_type(a);
        let wrapped = if matches!(&**a, T::App(..)) { format!("({arg})") } else { arg };
        return format!("{} {wrapped}", render_type(f));
    }
    match ty.to_string().as_str() {
        "Bool" => "Prop".into(),
        // Rocq has no `Int`/`Real`: the arithmetic types are `Z` and `R`.
        // Emitting the SMT-LIB spelling verbatim produced a file that
        // referenced identifiers Rocq does not have — a silent
        // mistranslation of exactly the kind constraint (1) rule 2 bans.
        "Int" => "Z".into(),
        "Real" => "R".into(),
        other => other.to_string(),
    }
}

/// A sort NAME as written in the declaration context, mapped the same
/// way [`render_type`] maps a `Type`.
fn render_sort_name(s: &str) -> String {
    match s {
        "Bool" => "Prop".to_owned(),
        "Int" => "Z".to_owned(),
        "Real" => "R".to_owned(),
        other => other.to_owned(),
    }
}

/// Which numeric theories the emitted file needs to import.
///
/// Checked against both the declaration context and the free variables,
/// because a cert built through [`adsmt_cert::recorder`] rather than the
/// CLI carries no signature.
fn numeric_imports(cert: &Certificate) -> (bool, bool) {
    let (mut z, mut r) = (false, false);
    let mut note = |t: &str| match t {
        "Int" => z = true,
        "Real" => r = true,
        _ => {}
    };
    // NOT the builtin sorts: the CLI registers `Int`/`Real`/`Bool`
    // unconditionally, so their presence says nothing about whether the
    // problem uses them. Only actual USES count.
    for s in cert.signature.sorts.iter().filter(|s| !s.builtin) {
        note(&s.name);
    }
    for f in &cert.signature.funs {
        for p in &f.params {
            note(p);
        }
        note(&f.result);
    }
    for d in &cert.signature.datatypes {
        for fs in &d.field_sorts {
            for f in fs {
                note(f);
            }
        }
    }
    for (_, ty) in collect_free_vars(cert) {
        if ty.contains('Z') {
            z = true;
        }
        if ty.contains('R') {
            r = true;
        }
    }
    (z, r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_cert::recorder::{recorder as r, ProofHandle};
    use adsmt_core::{Term, Type};

    fn p() -> Term {
        Term::var("p", Type::bool_())
    }


    /// A certificate whose declaration context exercises every shape:
    /// an uninterpreted sort, a datatype with a nullary and an
    /// argument-bearing constructor plus selectors, an uninterpreted
    /// function, and a defined function.
    fn cert_with_declarations() -> Certificate {
        use adsmt_cert::canonical::{DatatypeDecl, FunDecl};
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        b.declare_sort("Color", 0);
        b.declare_datatype(DatatypeDecl {
            sort_name: "Lst".into(),
            constructors: vec!["nil".into(), "cons".into()],
            arities: vec![0, 2],
            selectors: vec![vec![], vec!["hd".into(), "tl".into()]],
            field_sorts: vec![vec![], vec!["Int".into(), "Lst".into()]],
            params: vec![],
            is_finite: false,
        });
        b.declare_fun("f", vec!["Int".into()], "Bool", None);
        b.signature_mut().funs.push(FunDecl {
            name: "g".into(),
            params: vec!["Int".into()],
            param_names: vec!["x".into()],
            result: "Int".into(),
            body: Some("(+ x 1)".into()),
        });
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        b.snapshot(h.step())
    }

    /// Acceptance criterion, constraint (1) rule 3: every sort and every
    /// datatype of the input must appear in the output AS A DECLARATION.

    /// Rocq's type application is prefix, but the ARGUMENT still needs its
    /// own mapping — `Seq Int` names an `Int` Rocq does not have.
    #[test]
    fn a_higher_kinded_type_is_rendered_structurally() {
        use adsmt_core::Kind;
        let seq = Type::const_("Seq", Kind::arrow(Kind::Type, Kind::Type));
        let applied = Type::app(seq, Type::bool_()).unwrap();
        assert_eq!(render_type(&applied), "Seq Prop");
    }

    #[test]
    fn every_declared_sort_and_datatype_reaches_the_output() {
        let cert = cert_with_declarations();
        let s = emit_rocq(&cert);
        for sort in cert.signature.sorts.iter().filter(|s| !s.builtin) {
            let declared = s.contains(&format!("Parameter {} : Type.", sort.name))
                || s.contains(&format!("Inductive {}", sort.name));
            assert!(declared, "sort `{}` missing from output:\n{s}", sort.name);
        }
        for d in &cert.signature.datatypes {
            assert!(s.contains(&format!("Inductive {}", d.sort_name)), "{s}");
            for c in &d.constructors {
                assert!(s.contains(&format!("| {c} :")), "ctor `{c}` missing:\n{s}");
            }
        }
    }

    #[test]
    fn declarations_carry_arity_selectors_and_definitions() {
        let s = emit_rocq(&cert_with_declarations());
        // Rocq has no `Int`: the arithmetic type is `Z`, and emitting the
        // SMT-LIB spelling produced a file referencing an identifier Rocq
        // does not have.
        assert!(s.contains("| cons : Z -> Lst -> Lst"), "{s}");
        assert!(s.contains("| nil : Lst"), "{s}");
        assert!(s.contains("From Stdlib Require Import ZArith."), "{s}");
        // Selectors are partial in SMT-LIB: an axiom plus its
        // characteristic equation, not a total definition.
        assert!(s.contains("Parameter hd : Lst -> Z."), "{s}");
        assert!(s.contains("hd (cons x0 x1) = x0"), "{s}");
        assert!(s.contains("Parameter f : Z -> Prop."), "{s}");
        assert!(s.contains("Definition g (x : Z) : Z := (x + 1)."), "{s}");
        // A sort the datatype declares must not ALSO be an opaque
        // Parameter.
        assert!(!s.contains("Parameter Lst : Type."), "{s}");
        // An uninterpreted sort is non-empty in SMT-LIB; `Parameter S :
        // Type` alone does not say that in Rocq.
        assert!(s.contains("Axiom Color_nonempty : inhabited Color."), "{s}");
    }

    #[test]
    fn target_logic_and_build_declaration_travel_with_the_file() {
        // Constraint (2) rule 4: each backend states its OWN target-logic
        // binding rather than copying Isabelle's ROOT.
        let proj = emit_rocq_project();
        assert!(proj.contains("AdsmtCert.v"), "{proj}");
        let mut b = adsmt_cert::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let s = emit_rocq(&b.snapshot(h.step()));
        assert!(s.contains("Target logic: Rocq/Coq"), "{s}");
        assert!(s.contains("_CoqProject"), "{s}");
        // Trust surface must be countable from the artifact itself.
        assert!(s.contains("Print Assumptions AdsmtCert.result."), "{s}");
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
        assert!(s.contains("End AdsmtCert.\n"), "{s}");
        // The trust-surface query is the last thing in the file.
        assert!(s.ends_with("Print Assumptions AdsmtCert.result.\n"), "{s}");
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
        assert!(
            s.contains("(* USER-SUPPLIED ASSUMPTION (not proved): needs Functor MyType *)"),
            "{s}"
        );
        // A NAMED oracle axiom instead of `Admitted.`, and named
        // `adsmt_assumed_*` so `Print Assumptions` distinguishes a user
        // assumption from a theory decision (constraint (3)(C) rule 1).
        // Measured with coqc: the assumption is listed as
        // `AdsmtCert.adsmt_assumed_s0`.
        assert!(s.contains("Axiom adsmt_assumed_s0 : p."), "{s}");
        assert!(s.contains("Theorem s0 : p."), "{s}");
        assert!(s.contains("exact adsmt_assumed_s0."), "{s}");
        assert!(!s.contains("Admitted."), "{s}");
        assert!(s.contains("1 USER-SUPPLIED assumption(s)"), "{s}");
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

/// The Rocq build declaration for the emitted file.
///
/// Per constraint (2) rule 4 the Isabelle ROOT is NOT copied here: each
/// backend states its own target-logic binding. Rocq's is a `_CoqProject`
/// naming the file and the Ltac2 dependency.
pub fn emit_rocq_project() -> String {
    "-R . AdsmtCert\n-arg -w -arg -notation-overridden\nAdsmtCert.v\n".to_owned()
}

/// Constants the emitter knows how to render. Anything else is an
/// UNMAPPED symbol: adsmt's name is passed through verbatim, which is
/// how `> x 5` once reached Isabelle as prefix application and failed to
/// parse. Callers can ask for the list to surface the gap instead of
/// discovering it downstream.
pub fn unmapped_constants(cert: &Certificate) -> Vec<String> {
    const KNOWN: &[&str] = &[
        "true", "false", "not", "and", "or", "implies", "=>", "iff", "=",
        "<", "<=", ">", ">=", "+", "-", "*",
    ];
    let mut out: Vec<String> = Vec::new();
    fn walk(t: &Term, known: &[&str], out: &mut Vec<String>) {
        match t.kind() {
            TermInner::Const(c) => {
                let n = c.name.as_str();
                // Numeric literals render as themselves in every target.
                let numeric = !n.is_empty()
                    && n.chars().all(|ch| ch.is_ascii_digit() || ch == '-');
                if !numeric && !known.contains(&n) && !out.iter().any(|x| x == n) {
                    out.push(n.to_owned());
                }
            }
            TermInner::App(f, x) => {
                walk(&f, known, out);
                walk(&x, known, out);
            }
            TermInner::Lam(_, b) => walk(&b, known, out),
            _ => {}
        }
    }
    for step in &cert.steps {
        for h in &step.result.hyps {
            walk(h, KNOWN, &mut out);
        }
        walk(&step.result.concl, KNOWN, &mut out);
    }
    out
}

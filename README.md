# adsmt-contrib

Out-of-tree backends for the [adsmt](https://github.com/Honey-Be/adsmt-private)
SMT certificate pipeline.

| Crate | Role |
|---|---|
| [`adsmt-emit-rocq`](./adsmt-emit-rocq) | Rocq (Coq) certificate emit. Ltac1 excluded; emitted files set `Default Proof Mode "Ltac2"` and require Rocq ≥ 8.10. |
| [`adsmt-emit-isabelle`](./adsmt-emit-isabelle) | Isabelle/HOL certificate emit using the Isar proof language. |

Both crates mirror the in-tree `adsmt-cert::lean_emit` shape
exactly. The shared semantic anchors live in
`adsmt-cert::prover_emit::common` and propagate to every backend
unchanged — see `memory/prover_emit_policy.md` in the adsmt main
repo for the lockstep policy.

## License

Tri-licensed under any of:

- BSD-2-Clause
- Apache-2.0
- LGPL-2.1-or-later

(matches the adsmt main project's triple)

## Status

| Crate | Tests | Notes |
|---|---|---|
| `adsmt-emit-rocq` | 15/15 ✓ | Ltac2-only; mirrors Lean step mapping. v0.19: Trans + EqMp emit real proof terms (Rocq side K landed); two-pass scan=true wiring (A.5). |
| `adsmt-emit-isabelle` | 11/11 ✓ | HOL via Isar; `bool` for the proposition family. v0.19: two-pass scan=true wiring (A.5; no-op on Main-classical Isabelle but shape parity preserved). |

The proof-side of compound kernel rules (`Deduct`, `Abs`,
`Beta`, `Inst`, `InstType`) currently emits the *correct
statement type* with the proof body as a `sorry` / `Admitted.`
stub. Trans + EqMp already emit real proof terms on Rocq and
Lean. The remaining reconstruction is tracked in the adsmt v0.19
cycle (item 19A.1 K-full) and lands here lockstep across all
three backends.

## Adding a new ITP backend

When adding a fourth ITP target (HOL Light, Agda, …):

1. **Crate layout**: create a new workspace member
   `adsmt-emit-<itp>` following the existing two members'
   `Cargo.toml` shape (workspace deps on `adsmt-cert` and
   `adsmt-core`; tri-license; reused `description` style).
2. **Public API**: every backend exposes
   - `pub fn emit_<itp>(&Certificate) -> String` (hard-failing
     panic on missing classical imports).
   - `pub fn try_emit_<itp>(&Certificate) -> Result<String, MissingImports>`
     (fallible variant).
   - A `MissingImports` newtype wrapping
     `Vec<(StepId, ClassicalModuleFamily)>` — match Rocq /
     Isabelle's shape.
3. **Shared anchors**: every backend uses
   `adsmt_cert::prover_emit::common` for free-variable
   collection, `escape_for_comment`, `witness_summary`, the
   `*_axiom_keywords` table, the `*_import_line` mapper, and
   the aggregator / resolver / missing-imports trio.
   Bool → Prop / FunExt / etc. semantic decisions live there and
   propagate without backend-side reimplementation.
4. **Per-step mapping**: the policy document in the adsmt main
   repo's `memory/prover_emit_policy.md` § "Per-step mapping"
   has the canonical table. Trans + EqMp emit real proof terms;
   the remaining five compound rules (`Deduct / Abs / Beta /
   Inst / InstType`) emit "stub-shaped" placeholders with the
   correct statement type until v0.19's K-full reconstruction.
5. **Two-pass scan**: every backend implements the v0.19 A.5
   two-pass shape — `render_body(cert)` produces the
   preliminary text, `resolve_imports_with_scan(...,
   <backend>_axiom_keywords)` consumes it, the final emit lands
   with the resolved imports as prelude. Shape parity matters
   even when a particular backend's keyword table is empty
   (Isabelle's case).
6. **Tests**: every backend's `tests` module covers the same
   regression set the existing two cover — header presence,
   step-kind emission shapes, classical-import injection on
   should-marker presence, missing-imports detection,
   mid-block + pattern-marker propagation, scan-arm activation.
7. **Cross-prover output policy** lives in
   `memory/prover_emit_policy.md`. Any per-ITP syntactic
   adjustment that diverges from the policy needs explicit
   discussion before landing.

## Versioning

Each contrib backend ships independent semver. The in-tree
`adsmt-cert` dep is consumed via local path during development;
published builds switch to a git-rev or crates.io pin.

The contrib repo itself stays separate from the main adsmt repo
to keep the in-tree-Lean / out-of-tree-everything-else split
clean. v1.0 of adsmt will revisit the boundary.

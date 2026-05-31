# adsmt-contrib

Out-of-tree backends for the [adsmt](https://github.com/newsniper-org/adsmt)
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
| `adsmt-emit-rocq` | 15/15 ✓ | Ltac2-only; mirrors Lean step mapping. **v0.21 K-full**: every compound rule (`Trans`, `EqMp`, `Deduct`, `Abs`, `Beta`, `Inst`, `InstType`) emits real proof terms — no `Admitted.` stubs remain. **v0.19 A.5**: two-pass scan=true wiring. |
| `adsmt-emit-isabelle` | 11/11 ✓ | HOL via Isar; `bool` for the proposition family. **v0.21 K-full**: same as Rocq — every compound rule emits real Isar proof bodies. **v0.19 A.5**: two-pass scan=true wiring (no-op on Main-classical Isabelle but shape parity preserved). |

The compound-rule reconstruction completed across **all three
backends** (Lean / Rocq / Isabelle) by the close of adsmt's
v0.21 cycle. No backend ships `sorry` / `Admitted.` placeholders
for kernel-rule bodies any more.

### v0.23 phase 1 freeze implications

adsmt's v0.23 cycle landed the v1.0 phase 1 surface freeze
(C ABI / SMT-LIB dialect / certificate format). The cert AST
consumed by these backends — every `StepBody` variant, the 6
closed `StepPattern` variants + 3 derived helpers, the
`MidBlock` / `PatternMarker` cross-cutting shapes — is now
frozen under semver per `adsmt-cert/CERT_POLICY.md`. Adding a
new backend in this repo means consuming the frozen surface;
the lockstep rule in `prover_emit_policy.md` continues to
bind every backend's emit shape.

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
   has the canonical table. **All 12 StepBody variants** must
   be handled (Assume, Refl, Trans, Abs, Beta, EqMp, Deduct,
   Inst, InstType, Theory, Instance, Assumed); compound-rule
   real proof-term reconstruction is the v0.21 K-full
   baseline.
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

This contrib workspace tracks the **adsmt main version
directly** — currently `1.0.0`, aligned with adsmt main at
the v1.0.0 stable cut window (user instruction 2026-05-31).
The version field in this `Cargo.toml`'s `[workspace.package]`
matches `~/AD1/Cargo.toml`.

The in-tree `adsmt-cert` dep is consumed via local path
during development; published builds switch to a git-rev or
crates.io pin (see the commented-out alternative at the end
of `Cargo.toml`'s `[workspace.dependencies]` block —
post-v1.0 published form references the `v1.0.0` git tag).

## 21E.1 outcome — bidirectional embed

adsmt's v0.21 cycle settled the P5 architectural decision on
2026-05-30 as **option 5: bidirectional embed**. The
implications for this repo are:

- **Out-of-tree stays out-of-tree.** This repo continues to
  host the non-Lean backends; adsmt's in-tree `lean_emit` is
  the reference, and `~/adsmt-contrib/`'s Rocq + Isabelle
  backends mirror it under the lockstep rule.
- **No absorption into adsmt main.** The earlier "v1.0 of
  adsmt will revisit the boundary" language is settled — the
  boundary stays where it is.
- **Upstream contribution path is open.** Backends or shared
  anchors can flow upstream to OxiZ as Apache-2 contributions
  (per `memory/oxiz_relationship.md` § "P5 outcome") on the
  same cycle-by-cycle negotiation basis as the rest of the
  Path A+B integration.
- **License flow unchanged.** This repo stays triple BSD-2 /
  Apache-2 / LGPL-2.1+ matching adsmt main; OxiZ-side
  contributions go under Apache-2.

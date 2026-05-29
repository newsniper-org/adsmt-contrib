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
unchanged — see
`memory/prover_emit_policy.md` in the adsmt main repo for the
lockstep policy.

## License

Tri-licensed under any of:

- BSD-2-Clause
- Apache-2.0
- LGPL-2.1-or-later

(matches the adsmt main project's triple)

## Status

| Crate | Tests | Notes |
|---|---|---|
| `adsmt-emit-rocq` | 7/7 ✓ | Ltac2-only; mirrors Lean step mapping. |
| `adsmt-emit-isabelle` | 6/6 ✓ | HOL via Isar; `bool` for the proposition family. |

The proof-side of compound kernel rules (`Trans`, `EqMp`,
`Deduct`, `Abs`, `Beta`, `Inst`, `InstType`) currently emits the
*correct statement type* with the proof body as a `sorry` /
`Admitted.` stub. The full reconstruction is tracked in the
adsmt v0.17 cycle and lands here lockstep across all three
backends (Lean reference + Rocq + Isabelle mirrors).

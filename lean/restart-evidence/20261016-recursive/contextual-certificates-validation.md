# Static contextual branch certificates

Checked on 2026-10-16, Europe/Stockholm. Source frozen.

Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeContextualCertificates.lean`.
SHA256: `54eae2d8fa725cfdd6cd94bc69b5a21022f3d8284cf7cd5c2c6a856ec0d745e4`. Lines: 359.

## Validation

Focused canonical build: terminal 0, 1110 jobs. Only the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion` occurs.
Direct public probe: terminal 0. Sixteen public axiom reports, sixteen fully explicit public signatures, and nine kernel examples pass. The reports use only the standard foundations `propext`, `Classical.choice`, and `Quot.sound` (individual theorems may use fewer).

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextualCertificates
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-recursive/contextual-certificates-probe.lean
```

Exact outputs: `contextual-certificates-build.log` and `contextual-certificates-probe.log`. The probe and source snapshot remain in this directory. The kernel examples check empty and duplicate ordered walks, direct empty/reset/swap certificates, literal arity mismatch, actual contradictory source rejection, literal nested request order, and the exact yielded-prefix API.

## Derived contracts

- `node_walk_certified` and `edge_walk_certified` collect only local child laws and returned physical records in literal source order. Duplicate occurrences remain separate. Actual Extension retains earlier returned records through later child calls. Edge matching comes from the supplied exact request list; `compileRows_certified` derives it from actual `Kernel.pairs` membership.
- `compileRows_certified`, `left_union_certified`, and `right_union_certified` derive parent laws from those child laws and the actual constructor done equation. The fixed source facts and original resident operands identify original rows and members. The returned machine remains the machine used in that actual primitive equation.
- `empty_certified`, `reset_certified`, `swap_certified`, `repeated_certified`, and `self_certified` use the existing independent branch laws. Repeated cutoff retains the actual identities, nonempty operands, and seen pair. Self reuse retains actual coherent source availability and the actual closed-self condition.
- `children_certified` derives the accepted edge law from equal arity, matching symbols, literal combined guard truth, ordered local node laws, and actual makeEdge fields. `children_source_certified` discharges the truth equation from literal source conjunction readback with the actual PCS guard theorem.
- `sentinel_certified` derives its law from a literal empty child and independent original ranked-row disjointness. `mismatch_certified` derives that disjointness from original arities. `rejected_certified` derives it from actual pure source rejection and normalized original fields.
- `prefix_certified` consumes the literal actual yielded checked edge prefix. Current Good and EdgeReady derive original Cached fields. Actual read-only loads and completed equality-prefix receipts select rejection or accepted child code. Equal original arities rule out the inner mismatch branch. No parent trace, supplied final invariant, or parent result law occurs in its premises.

## Scope

These are static `ContextualCode.Certified` proofs. The generic interpreter separately executes them with actual child-local induction hypotheses. The certificates do not assume a completed parent body or prove general execution termination themselves. Mu entry and bound-reference resolution, plus final compileNode dispatch, are owned by the separate integration modules. The checked edge prefix is used directly; no equality of effects with the historical eager edge compiler is asserted. Result closedness, whole original-language exactness, GHC forcing/publication, concurrency, and finite machine-key capacity remain separate obligations. No older proof, Haskell file, Audit, documentation, or Git metadata was edited by this worker.

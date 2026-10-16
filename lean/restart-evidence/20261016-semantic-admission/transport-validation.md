# Same-source input inventory and contextual cache transport

Timestamp: 2026-10-16 07:14 CEST.

Owned source: `lean/MicroCFTA/SourceCurrentAllocatedNativeInputModelTransport.lean`.
SHA256: `be76b241e61676347adb1bf1de09d8f6bb3b5c049f91274740bb1c7d19f297dc`.
The 150-line source is frozen. Current Haskell main remains `8f85ddb6`.

Canonical focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport
```

Result: terminal exit 0, 1063 jobs. No new warnings. The existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean:24` replayed. Raw log: `transport-build.log`. Canonical build ownership was coordinated with the parent and released after this terminal result.

Direct public probe command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-semantic-admission/transport-probe.lean
```

Result: terminal exit 0, no warnings. Fourteen public declaration axiom checks and fourteen signatures passed. Four kernel examples passed. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Raw log: `transport-probe.log`.

## Derived APIs

The namespace is `SourceCurrentAllocatedNativeInputModelTransport`.

`ranks_eq view before after sameRepresentative` derives equality of all finite derivation ranks. `languages_eq` derives equality after rank erasure. These depend only on the same view and representative function. They impose no valid-domain membership condition.

`reachable_mono source holds oldRoots newRoots included input reachable` derives actual input reachability under literal root-list inclusion. `inventory_valid` applies this to the existing `InputInventoryModels.finiteInput`. `inventory_representative`, `inventory_ranks`, and `inventory_languages` prove exact equality for actual root inventories in the same source heap. All three equality proofs are `rfl`; the representative does not depend on the root list. Lists can retain arbitrary source order and duplicate occurrences.

`Admitted view model state` records old admission of every returned request. Its fields are:

- `nodes : Returned (fun request _ => NodeInputs view model request) state.nodes`.
- `edges : Returned (fun request _ => EdgeInputs view model request) state.edges`.

This certificate contains no result-language law. It is independent of physical validity, `Contextual`, and scope. `initial_admitted` derives it for empty native tables. `advance_admitted` retains it through literal machine advance. `admitted_mono` transports it through a valid-domain inclusion.

`node_law view oldInputs newInputs sameRepresentative holds request result oldAdmission oldLaw` derives the contextual node law in the new finite model. `edge_law` does the same for actual returned rows. Each proof first supplies OLD admission to the old conditional law, then rewrites the identical languages and ranks. No new result law is a premise. New membership alone is not used to justify old behavior.

`contextual view oldInputs newInputs sameRepresentative holds state admitted oldContextual` transfers both returned native cell families on the same actual state. This theorem does not change tables, heap, domains, requests, or results. Root-list inclusion also gives new `Admitted` through `inventory_valid` and `admitted_mono`.

## Kernel checks and boundary

The four examples establish:

1. Actual root-list inclusion grows validity and preserves all ranks and languages.
2. Actual same-source inventories transfer both returned-cell families and their admission certificate, without a supplied new cache law.
3. Cold native tables derive admission and contextual transport into a same-representative model.
4. A formal obstruction to removing old admission: if a request is excluded by the old model but admitted by the new model with a common finite derivation and an empty seen domain, the empty result has a vacuous old `NodeLaw` but cannot have the new `NodeLaw`. This is a conditional kernel statement, not a claim of a concrete Haskell defect.

The source heap and input view remain fixed throughout this module. Closed original root inventories, actual source availability, and source facts are supplied to the existing finite inventory constructor. Cached-request admission remains explicit for nonempty warm caches. It is not derived from `Good`, physical residency, scope, or `Contextual` alone.

The module does not admit newly allocated values from a later heap, transport views across heap growth, preserve ranks across different representatives, derive causal coverage at native finishes, or prove the checked seeded class witness. Those are the next obligations. It also makes no GHC forcing, publication, concrete container, allocation order, or concurrency claim. No old proof source, Audit, documentation, Haskell source, or Git state was changed.

# Fixed input inventory validation

Validated at 2026-10-16 06:26 CEST.

The new module `SourceCurrentAllocatedNativeInputInventoryModels.lean` has 119 lines. Its frozen SHA256 is `7c4f83cf02014d7046a46f5099c283f66fa93931660b22d746bbac198648bb6e`.

`Reachable` is the union of actual input reachability from the listed physical roots. `finiteInput` uses this domain and the existing common physical representative. The premises require every listed root to be Original, available in the fixed source heap, and closed. Actual closed-root reachability derives original records, canonical representatives, and containment in the finite issued carrier. The interface derives body, reference, row-child, and union-member closure. It performs no union allocation.

`root_valid` gives validity in this exact interface. `root_language` gives physical readback into its exact `finiteInputMeaning`. `source_input_models` returns one model, one independent rank family, validity for all listed roots, finite-rank language equivalence, and physical language readback for every listed root. No result law, source-model validity callback, or child completion is a premise. The domain does not claim to contain every arbitrary OriginalInput in the heap.

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels
```

Result: terminal 0, 455 jobs, no warnings. The raw log is `inventory-build-20261016.log`.

Standalone command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-warm-history/inventory-public-probes-20261016.lean
```

Result: terminal 0, no warnings. All seven public declaration axiom reports and seven signatures pass. Only the standard `propext`, `Classical.choice`, and `Quot.sound` foundations occur. All 14 kernel examples pass. They cover the empty list, shared root validity, duplicate and reordered inventories, structural closure, the common representative, warm-history pair premises, finite carrier membership, exact physical language, shared ranks, and exclusion of a free original reference from the closed-root contract.

Only the new proof module and new `inventory-*` evidence files were written. No old proof, Audit, documentation, Haskell, or Git mutation was performed. The separate warm-query source review is recorded in `inventory-review.md`.

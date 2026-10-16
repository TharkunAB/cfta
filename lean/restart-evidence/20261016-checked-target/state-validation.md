# Allocated shared target state validation

Validated 2026-10-16 09:01 CEST with pinned Lean v4.34.1.

Source: `MicroCFTA/SourceCurrentAllocatedSharedTargetState.lean`.
SHA256: 309565fe00740f6e2c92072a2f99921dfd5567125ac59de6faf5ceba372d0385.

`State width` retains the full checked state, class-local path slots, and the warm completed merge memo. `initial checked memo` clears only slots. No native table, equality operation, domain cache, physical heap, or merge memo is reset.

`SlotReceipt width formulas solver record values heap memo path value` retains membership, existential historical checked start/return states, a historical computed inventory, initial/returned merge memos, historical global bundles, the actual new Target graph, exact TargetReads, full TargetComplete.Receipt, heap Keeps, and merge Extends. Historical and current inventories are not identified. The captured forest is fixed. Closed availability and independent SelectedIncludes follow from the historical receipt and current Keeps. They require no new whole-forest domain or current cache-semantic law.

Ready retains current checked readiness and Inventory.At, captured heap Keeps, current merge Stored, uniform ambient CacheCovers, and each present slot's historical receipt. `Ready.advance` is transition bookkeeping: it consumes actual physical Effects and the locally derived next checked Ready/At. `Ready.physical` derives those two next invariants itself from actual constructor Effects. `Ready.store` consumes the same actual completed Target, TargetReads, and its derived Receipt. It installs the computed inventory and retains every distinct old slot by Keeps/Extends. It does not require a final-slot receipt as an input. Slot retention when storing at a missing path belongs to Force, which supplies the actual none test.

Focused build:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedSharedTargetState
```

Terminal exit 0, 1281 jobs, no new warning. The preexisting unused-input warning was replayed. First direct elaboration needed only qualified state advance/store names to avoid the corresponding Ready theorem names. No frozen source was edited.

Direct probes:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-target/state-public.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-target/state-kernels.lean
```

Both terminal exit 0/no warnings. Seven public theorem axiom reports and seven signature checks passed, with only propext, Classical.choice, and Quot.sound. Seven kernel compositions passed: exact initial state/table retention, historical closed availability through growth, historical selected meaning without current At, constructor effects deriving current admission, inventory change retaining an old slot, storing a target retaining a distinct slot, and the new slot's derived admission/closedness/selected language.

The module does not prove forcing completion by itself. Root/Force modules derive actual calls and their receipts. Completed graph/runtime forcing, native containers, and the pure selection noConstraint CAF adapter remain separate. No old source, Audit, documentation, Haskell, or Git state was changed. Derived evidence-only olean was removed; text, raw logs, and hashes remain.

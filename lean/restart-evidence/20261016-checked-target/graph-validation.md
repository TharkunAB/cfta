# Raw allocated target graph validation

Validated 2026-10-16 08:54 CEST with pinned Lean v4.34.1.

Source: `MicroCFTA/SourceCurrentAllocatedTargetGraph.lean`.
SHA256: 7685d0546656c13d3048580cc33abf1bd448da3b89be56ebf60bb9e6c7719395.

The module adds only the literal current Operand, Fold, Target graphs and reached range plans. The physical state is the complete checked NativeDemand state. The merge memo remains a separate explicit table. Operand executes actual Forest, then allocated Merge with literalClear at exactly `advancePhysical before (projectedHeap, before.operations)`. Fold nil evaluates its seed operand. Fold cons evaluates its head operand, recursive tail, then actual TargetQuery.Step of those literal returned values at the tail-return state. The checked step leaves the separately threaded merge memo at the tail's returned table. Target nil returns EmptyNode unchanged; nonempty uses the source first operand as final fold seed.

`FoldRanges` contains only checks over actual raw Operand and recursive Fold prefixes. It asks for WordRanges on the exact head/tail request at the actual returned checked state. It has no semantic result, inventory model, callback success, future field closure, or native completion premise. Its empty branch is True. `TargetRanges` selects the same literal first seed as Target.

Public endpoints:

- `Operand.verified formulas solver inventory actual ready admitted available domain stored covered memos valid` constructs the existing MergeOperand.Receipt at that actual graph's SAME output, complete checked state, and merge memo.
- `of_receipt receipt` reads that raw graph back from the existing receipt.
- `Operand.complete` uses the same initial assumptions and constructs raw graph plus receipt. Only selected ForestClosed is required; unrelated siblings can remain open.
- Operand/Fold/Target `extends` retain every earlier completed merge entry.

The selected domain is explicit. An empty selected path retains its existing whole-forest root domain. Uniform CacheCovers is an initial warm merge-cache invariant, not a future-result law. Global table validity is also initial. The graph does not prove full Fold/Target semantic completion; the separate parent module composes the actual native queries and changing inventories. No Haskell demand order, pending memo forcing, native container order, or selection CAF-allocation adapter is established here.

Focused canonical command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedTargetGraph
```

Terminal exit 0, 1277 jobs. No new warnings. Only the old unused-input warning from InternedFreshOrdinaryClosedCompletion was replayed.

Direct commands:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-target/graph-public.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-target/graph-kernels.lean
```

Both terminal exit 0, no warnings. Six public theorem axiom reports and six signatures passed. Axioms are limited to propext, Classical.choice, and Quot.sound. Seven kernel compositions passed: exact projection-to-merge state, finite raw operand with retained native fields, actual-operand selected-term inclusion, actual-prefix ranges, literal two-path source order, empty target unchanged, and old merge entries retained through the actual Fold.

No prior source, Haskell, Audit, documentation, or Git state was modified. Derived evidence-only olean was removed after canonical release. Frozen source/probe text and raw logs remain in this directory.

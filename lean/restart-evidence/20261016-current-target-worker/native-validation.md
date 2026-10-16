# Native target return bridge

Source: `MicroCFTA/SourceCurrentAllocatedTargetWorkerNative.lean`.

The public `of_done` theorem consumes the supplied literal checked execution.
Its entry premises are `Good`, idle native cells, resident left and right
operands, empty operand free lists, and reached `WordRanges` for that request.
It has no final invariant, physical trace, semantic result law, inventory,
global memo law, or completed callback premise.

`Good.native.machine.1` supplies coherent constructor records.
`SourceRecursiveIntersectionOriginalOutput.closed_original` then derives
original operand syntax. `PhysicalTraceCompletion.initial_complete`
constructs an independent physical trace. Its pure guard interpretation is
constant true. That interpretation supplies the request schedule only.
It is not a PCS language conclusion. `ColdClosedExact.completed_unique`
identifies the constructed return with the supplied return, including every
checked state field. `of_done_ready` consumes the existing class-scan Ready
structure instead of separate Good and idle proofs. `step_iff_done` records
the equivalence on this initial physical domain.

This closes the physical trace gap for the target worker's completed native
stage. Arbitrary native completion outside this initial domain still does
not supply physical input checks. Semantic use of `Step.verified` still
requires the initial inventory admission and coherent global memo bundle.
This module does not infer contextual language laws from physical Good.

## Validation

Pinned toolchain: `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin`.

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedTargetWorkerNative.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedTargetWorkerNative
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-target-worker/native-public.lean
```

All three commands returned exit 0. `native-direct-1.log` has no warning.
`native-build-1.log` records 1234 jobs and only the existing unused-input
warning in `InternedFreshOrdinaryClosedCompletion`. `native-public-1.log`
has three public axiom checks, three full signatures, and four checked
external examples. The examples compose the supplied native return with
same-return language and global memo receipts, retain success under extra
fuel, admit duplicate Empty operands without an Original or inventory
premise, and retain the literal yielded observation at zero fuel.
The public dependencies use only `propext`, `Classical.choice`, and
`Quot.sound`. No source changed after these commands.

The focused Lake slot is released. No owned process remains. No Haskell,
older Lean source, Audit, project documentation, or Git metadata was edited.

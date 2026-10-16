# Actual local and parent receipts: foundation validation

The checked source is Lean 4.34.1. This increment changes new proof files only.

## Frozen foundation

- `SourceCurrentAllocatedConjunctionReadValidity.lean`: SHA256 `667392991e6011cdc4b66d43b574e5a54d3cad9cf28a6ce89e681091d0b69426`.
- `SourceCurrentConjunctionRequiredActual.lean`: SHA256 `f4e2dfe08e8ec2cb1cce7dde006ae83b57ba1d2050afd2b646a39b093718aef3`.

Command:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity MicroCFTA.SourceCurrentConjunctionRequiredActual
```

Result: terminal 0, 1,267 jobs. The log is `actual-foundation-build-1.log`. Only the existing dependency unused-input warning occurs. Both new files have no warning.

Direct public probe:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-caller-invariants/actual-foundation-public.lean
```

Result: terminal 0, 13 public axiom checks, 13 full signatures, and eight external kernel examples. There are no errors or warnings. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Raw output is `actual-foundation-public-3.log`. Machine-readable status is `actual-foundation-checks.json`.

## Derived contracts

`ConjunctionReadValidity.call reads ready available valid` derives validity of the supplied returned three-table bundle, unfolding-table retention, and unchanged predicate/descendant query tables. The induction follows the supplied reads through exposure, row-major projections, equality tuple allocation, worklist admission, and fourth-memo hit or miss. The proof derives the physical state for each following operation from existing actual graph effects. It does not replace the supplied saved bundle with an existentially constructed one.

`RequiredActual.required_unique` derives value and constructor-heap equality for two completed literal `requireAll` calls at arbitrary completed bounds. It uses actual graph conversion and `children_unique`. This equality concerns results and constructor heaps. It does not identify global memo schedules.

`RequiredActual.verified` derives the required receipt for the supplied completed continuation of the actual Scan. The finite required call supplies a receipt. Completed graph uniqueness transports it to the supplied result and heap. No final readiness, language, or memo-validity premise is supplied.

## Source order

`cfta/src/Data/CFTA/Equality/Operations.hs:164-168` calls `mkEdge` with the original symbol and full raw constraint and the local child reduction. `Interned/Type.hs:566-568` tests raw contradiction first. That rejection does not need the local child list.

`Equality/Operations.hs:207-222` selects unchanged, contradictory, refused-class stop, or continuation. `:226` runs required paths before the class right fold at `:211`. `:236-242` retains ordered class path edits and their captured current forest.

The operational graphs retain the completed serial schedule. These proofs do not establish GHC forcing, lazy publication, native HashMap/IntMap representation, machine identity capacity, or general recursive caller completion.

## Additional actual adapters

`SourceCurrentConjunctionScanClassPassActual`, `SourceCurrentAllocatedLocalReductionActual`, and `SourceCurrentAllocatedParentEdgeActual` are in progress. Their semantic and physical derivation uses the supplied continuation. Actual verification needs only reached Scan ranges. It does not need future class-pass completion ranges.

The root found an older primary `NodeReads.endpoint_closed` indexing defect: its memo-call operand is not tied to the node of the indexed endpoint trace. Consequently arbitrary historical primary Reads do not imply final global validity. An additive exact source-call anchor is required for the new actual adapters. No unconditioned whole-parent result is claimed while that bridge is pending. This is a Lean receipt defect, not a reported Haskell defect.

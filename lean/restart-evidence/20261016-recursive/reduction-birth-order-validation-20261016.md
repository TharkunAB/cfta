# Reduction birth-order component

Date: 2026-10-16 04:58 CEST.
Read-only validation HEAD: `43b910be5c37571066da594fe25fe917feab84da`.
Source: `lean/MicroCFTA/SourceCurrentReductionBirthOrder.lean`.
SHA256: `704b0c1ee0824d1489388545117d9f3ccd181c77f34bddd3a4fb91616eb18432`.
Length: 466 lines.

## Derived result

The finite model follows the source table precedence in `Gen/Synthesis.hs:625-672`.

- `recordRound` uses the existing `GroupPositions.insertFirst` update. The birth index advances between rounds, not between edges. `births_exact` returns exactly the earliest observed occurrence, and `births_bound` places it inside the finite history.
- `fromMinEntries` retains the minimum of colliding entries. `foldMin_lookup` proves that this specification equals the literal left insertion fold. `transportEntries_mem` derives each mapped entry from an observed original/mapped pair and an actual successful original birth lookup.
- `rounds` performs minimum union of original births with the mapped-entry table. `rounds_exact` proves that the result is exactly the earliest original or observed refold-preimage birth. It is not a left-biased union.
- `history_rounds_rename` derives lookup invariance when all observed keys are renamed injectively. It composes the first-birth, mapped-entry, and minimum-union laws. It does not assume the resulting table equality.
- `rounds_bound`, `index_unknown`, and `known_before_unknown` prove that known births precede the history-length fallback for unknown edges.
- The separate bounded `reductions` worker follows the source equality stop and finite fuel stop. `source_history_bound` gives a nonempty history of at most 31 spaces for the fixed bound 30. Arbitrary public `orderedSpace` histories are not assumed to satisfy this bound.

## Scope

Observed round edge lists and original/mapped edge pairs are finite model inputs. The source traversal and its cross-round visited-node optimization still need a faithful immutable-identity adapter. The model uses extensional tables; native IntMap behavior and machine key bounds remain adapters. Actual `refoldEdges` traversal, shared `mapNodes` effects, stabilization, edge correspondence, and language preservation remain adapters. Double conversion and stable canonical-weight sorting remain adapters, as does exact enumeration behavior. The source `orderedSpace []` error is not modeled as a successful Space construction. This module makes no process-history independence, whole-source language, runtime, allocation, or exact global enumeration-order claim.

The normal source bound makes its round indices small, but this module does not assert an IEEE Double conversion theorem. Injectivity of the key correspondence is explicit and necessary; one kernel check refutes invariance for a noninjective renaming.

## Validation

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentReductionBirthOrder
```

PASS exit 0, 14 jobs, no warning. Log: `reduction-birth-order-build-20261016.log`.

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/reduction-birth-order-public-probes-20261016.lean
```

PASS exit 0, no warning. All 32 public theorem axiom reports, 10 public signatures, and 14 concrete kernel checks pass. Maximum axiom set: `propext`, `Classical.choice`, `Quot.sound`. No custom axiom or `sorryAx` occurs. The source has no `sorry`, `admit`, or `axiom` declaration.

Kernel checks cover round indexing, first-wins chronology, signed keys, minimum refold collisions, earlier-original and earlier-mapped precedence, absent original preimages, literal left minimum fold, fallback, signed order-reversing injective renaming, a noninjective counterexample, a stable one-space reduction, an always-changing 31-space reduction, and an arbitrary 40-space history.

## Preservation

Only this new proof module and owned new evidence files were added. MuMeaning and all older proof sources remain unchanged. No production Haskell, Audit, repository documentation, Git, or sibling file was edited. A source snapshot and SHA256 manifest are in this directory. No owned process remains.

# Independent allocated current Scan validation

Date: 2026-10-16 08:05 CEST.

Source: `lean/MicroCFTA/SourceCurrentConjunctionAllocatedScanSoundness.lean`.

Source SHA256: `0f5d7a8498d491ac70637baf08de9c5aa8cfc6914772388d93ee05c21db80a00`.

The root reported canonical build GREEN1324. The independent direct Lean check passed with exit status 0 on the first attempt. The log contains no errors, warnings, or `sorryAx`. No canonical Lake build ran.

Command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-seeded-language/allocated-scan-independent-probes.lean
```

## Counts

Both public theorem endpoints, `prefix_admitted` and `finite`, have axiom reports and complete signature checks. The `emptyInventory` definition also has its complete signature checked. Three named integration kernels have their own axiom reports and complete signatures.

Totals: two public theorem axiom reports, three public signatures, three kernel axiom reports, and three kernel signatures. All five axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## Kernel integrations

`prefix_exact` uses `prefix_admitted` and the literal `prefixState` definition. It derives At for the empty-root inventory, both native memo tables equal to `FlatMemoThunk.empty`, the exact original machine with empty domains, and equality of the checked operation state to the actual returned `precheck ... (initialOperations cache)` second component. It does not reset that returned operation state or supply a completed native result law.

`finite_empty_fourth` applies the full constructed finite endpoint with `SourceCurrentEmptinessMemo.empty`. It derives its initial Correct proof through `empty_correct`; the kernel has no Correct premise. Actual allocation History, initial cache validity, source guard coverage, a completed fresh original build, and resident edge yield the same-cache loaded constraint. For each ready inherited constraint and actual successful precheck class output, the actual-prefix range plan yields a completed current Scan, final Ready, final At, final fourth-memo correctness, and soundness of every rejected original class. It supplies no initial Good, Ready, Scoped, model-validity proof, class properness callback, completed Scan, or desired language law.

`stopped_constraints_impossible` composes that constructed empty-memo endpoint. A stopped Scan identifies its rejected class among the actual precheck output classes. Hence no original child forest accepted under any ambient environment can satisfy all `output.map Record.paths` classes. The contradiction uses only accepted child languages, actual class membership, and the derived stopped-class law.

## Scope

The initial allocation History, initial interner cache validity, literal original-build completion, guard coverage by that history, resident edge, ready inherited constraint, actual precheck output, and actual-prefix reached ranges remain explicit. These are the entry premises, not desired future Scan or result laws. The actual native tables start empty; the fourth table also starts empty in the integration kernel. The proofs derive later physical and semantic cache laws.

The stopped result refutes the actual precheck equality classes on every accepted original child forest. It does not establish the later required-path edits, shared class-target execution, the outer Haskell caller, solver IO correctness, or GHC runtime correspondence. The source header states the later-edit and caller boundary explicitly.

No source defect was found by these checks. Only new evidence files were written. No proof source, Audit, documentation, Git, or Haskell file was edited.

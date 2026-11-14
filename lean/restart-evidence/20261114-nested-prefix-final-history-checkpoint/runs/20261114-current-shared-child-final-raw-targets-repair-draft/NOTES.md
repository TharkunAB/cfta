# Final raw-target proof repair

Status: UNCOMPILED CANDIDATE. The root owns validation and publication.

Source:
`SourcePruningEnumerationSharedChildFinalRawTargets.lean`

SHA256:
`5289a36cc3fa7ee8bd84ae4f57a404a4ed718ea4dcaf5961f220f7f9d3304f05`

The frozen original failed strict elaboration. The log is
`20261114-general-row-and-final-alias-check/final-raw-targets-1.txt`.
The failed axiom probe contains `sorryAx`. It gives no proof credit.

This repair changes only two proof sites:

- Remove the redundant `rfl` after `rw [← coreSame]`.
- End the first `all_goals` block after its final branch-closing `try`.
  Use a second `all_goals` block for the remaining incoming-success cases.

All four explicit theorem headers match the frozen original byte for byte.
Reversing these two edits recovers that entire module exactly. The public
statement, all intermediate endpoints and all premises remain unchanged.
The original packet and failure log remain intact.

Public probe:

```lean
#print axioms MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_final_raw_target_incidence
```

The candidate keeps the exact terminal partition and duplicate-preserving
recorded list. It derives raw-target aliases at joined, folded, read and
returned Cores from actual shared operations. It adds no alias, native,
semantic-model, assignment or future-result premise.

The MAIN full finite-witness target remains open. The same original emitted
root needs ONE finite accepted completion under ONE assignment satisfying
all retained and historical removed obligations. Earlier-entry alignment,
later-clear matching and emitted-history extraction remain open. The full
target and initializer remain pinned. No Haskell fix or failing source trace
was established. No live source, Git, board, compiler or temporary work ran.

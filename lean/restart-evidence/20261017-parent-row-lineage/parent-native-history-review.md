# Parent native history review

The source is `SourceCurrentParentNativeHistory.lean`.
Its final SHA256 is `3c88c79958b914299db33ca5875f7795c3e48da99febb56eb6c17377ef1bac64`.
The module has eight public theorem declarations. It adds no datatype or constructor.

## Checked contract

`target`, `force`, and `leaf` use actual completed read receipts.
Native requests extend the history with their literal checked traces.
Physical stages retain the complete native tables and domain state.
Each physical advance records growth of the actual earlier constructor heap.
Equality-operation state remains the actual returned state.

`edit_node`, `edit_children`, and `edit_rows` take their actual Reads,
initial History, and constructor Valid. They return History and constructor
Valid at the exact returned heap. The mutual child induction checks the
actual recursive Head, selected leaf receipts, and raw row and node work.
Rows reuse that checked child transport. Nodes reuse the row transport.
There is no Cap, whole-forest closure, range, or per-stage history premise.

`class_pass` takes actual PassReads, initial History, and initial Ready.
It covers the full tail-first class fold and the final empty propagation.
It adds no range or conditional target-store predicate.

`parent` transports actual Parent Reads through precheck, gates, seeded
queries, current conjunction, Required, ClassPass, and final construction.
It uses initial Ready, At, cached field/load, inherited readiness, original
value availability, fourth-memo correctness, and the EXISTING Parent.Ranges.
The range plan retains its original conditional reached-query word bounds.
It supplies no desired writer law or completed future call.
The scan proof uses that plan to recover legitimate supported operand
readiness at actual reached queries. It does not remove the range plan.
Required growth comes from its actual completed requireAll equation.
The final constructor uses run_correct and the literal build equation.

## Scope

These are completed-graph transport theorems. They do not produce general
outer completion, a decreasing origin rank, node-owner exclusion, retained
Mu reconstruction equality, or Haskell correspondence. Initial History
records earlier actual executions. No new theorem assumes a desired writer
predicate for future execution. Generated writer handles and their growth
remain available through the existing History.writers interface.

## Constructed integrations

The private initial setup is copied from the immutable earlier
`20261017-initial-parent/parent-numeric-kernels-1.source.lean`.
It constructs its own full source, fields, Ready, Frame, Fits, caller Context,
empty memo laws, and available original forest. The forest contains a
finite ordinary root, a constrained productive Mu outside every finite Cap,
and an unrelated open depth reference.

`constructed_class_pass` chooses a finite bit width from the symbolic final
profile, proves the selected proper domains, and invokes the existing
initial ClassCallerNumeric.complete. It then applies class_pass to the
new actual Reads. It returns History, Frame, Fits, and unchanged forest
length. The selected class is nonempty. The theorem does not assert a
specific returned native cell or test retained-Mu recursive reconstruction.

`constructed_parent` invokes initial ParentNumeric.complete at width two.
Its actual empty own/inherited precheck returns unchanged. The initial
Parent range plan is discharged because a classes branch contradicts that
exact precheck equation. The literal parent constructor then retains History.
This fixture does not run the Parent classes branch. That branch is covered
by the general completed-graph theorem, while the separate class fixture
exercises a nonempty pass. Neither fixture takes a supplied future trace,
result, receipt, room, or History as an input.

## Verification and attempt history

Selected strict: parent-native-history-direct-16, exit 0, log 0 bytes.
Selected canonical: parent-native-history-canonical-3, exit 0, 1406 jobs.
The canonical log replays the unchanged ClosedCompletion unused-input warning.
There is no warning from the new final production source.
Selected imported public: public-1, eight full signature/proof/axiom groups.
Selected constructed: kernels-7, two full signature/proof/axiom groups.
All selected axioms are propext, Classical.choice, and Quot.sound only.
All eight explicit probe options are present. No printer omission is allowed.
All runs record effective Max=High=4294967296 bytes and SwapMax=0.

All numbered source attempts and raw logs remain present. Attempts 1–15
include failed elaboration or earlier successful but warning-bearing proofs.
Some earlier chat reports incorrectly called pass logs EMPTY before wc.
Only direct-16 is selected as the final empty strict receipt. This record
corrects those descriptions without changing any earlier source or log.
Canonical-1 built the partial direct-10 source. Canonical-2 built direct-14.
Canonical-3 built final direct-16. Kernel attempts 1–6 preserve the failed
syntax and selected-domain proof attempts. Kernel-7 is the selected success.

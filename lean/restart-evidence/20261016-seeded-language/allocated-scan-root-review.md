# Allocated current scan soundness review

Date: 2026-10-16 08:04 CEST.
Read-only review. No build or proof edit ran.

## Verdict

No material defect found in the final checked source. The public
constructed endpoint has no initial `At`, contextual cache law, operand
admission, active-class, proper-path, or final-state invariant premise.
It derives these facts from the explicit allocation/construction receipts
and from the actual live precheck. It returns an actual final inventory
and `At` in addition to physical invariants and stopped-class soundness.

## Entry and cold inventory

`AllocatedClassEntry.prefixState` (lines 39-42) uses cold native tables and
the exact operation state returned by the actual accessor/precheck.
`AllocatedScanSoundness.prefix_admitted` (lines 48-54) applies the empty
table inventory theorem to this literal state. An empty root inventory is
sufficient because the native tables are empty. No request law or input
admission is inferred from a conditional semantic law.

The native inventory does not assert that every original child is closed.
The constructed resident edge supplies original child availability.
Projection support later derives closed native operands. Each actual
native query then constructs its expanded concrete inventory.

`AllocatedClassEntry.entry` derives the resident raw-field load, literal
constraint readback, and stored-payload readiness from the covered
allocation history and actual source build. It runs the actual own
accessor before the native precheck. It retains the returned operations
and derives physical readiness through their proved growth. It derives
proper paths and coherent/ascending/nontrivial original records from the
live precheck receipt. `AllocatedScanSoundness.finite` uses those derived
record facts for its active-class premise (lines 94-107).

The source tests contradiction on the combination of own and inherited
equalities, but partitions the ordered own classes
(`cfta/src/Data/CFTA/Equality/Operations.hs:207-224`). The wrapper preserves
this distinction. It does not scan combined inherited classes or replace
the own payload with the raw stored field.

## Finite scan and stopped semantics

The finite endpoint first constructs an actual current `Scan` using only
the physical completion theorem and reached ranges. It then applies
`ClassScanSoundness.verified` to that same trace. No completed Scan is a
public premise. The latter theorem derives changing concrete inventories,
physical effects, returned memo correctness, and the stop law.

In `ClassScanSoundness`, gate branches retain the same native cells.
Continued and stopped branches obtain the exact actual seeded receipt by
uniqueness. The current conjunction memo advances that inventory through
its actual returned physical state. False answers carry the returned
memo into the suffix. True answers stop without a suffix completion or
suffix range premise.

At a stop, nontriviality and `ClassSat` derive a common selected subtree.
The independently proved seeded inclusion puts that subtree in the actual
query language. The current conjunction memo's derived `AnswerSound`
then contradicts acceptance. There is no supplied accepted-row, query
language, or desired root-result oracle. The final wrapper also proves
that the rejected class is a literal member of the original output list.
It makes no claim that selected records after a stop include the unvisited
suffix.

## Explicit remaining premises and limits

The endpoint still requires allocation `History`, a valid initial equality
interner, syntax-field history coverage, an actual closed-environment
source build, resident edge, ready inherited physical payload, actual live
precheck receipt, initial conservative fourth-memo correctness, and
reached `Ranges`. These are visible input conditions. The finite Scan and
its final inventory/cache laws are conclusions.

The initial operation tables are the documented cold completed-cache
projection over the retained interner. This does not model a reset of
production global tables or derive their global unsafe-IO initialization.
The theorem refutes the stopped class on independently accepted original
child forests. It does not yet prove later required-path edits, the entire
constrained caller, global gate memo publication/forcing, host table or
machine-identity adequacy, or GHC evaluation order.

## Evidence inspected

Final `allocated-scan-build-3.log` records terminal success for 1324 jobs.
Its only warning is the preexisting unused `inputs` binder.
The first build's structure-literal syntax error was repaired in the
root-owned source. No semantic issue arose from that repair.
`ClassScanSoundness` was reported frozen at canonical 1232 jobs; its
final source was inspected directly.

```text
0f5d7a8498d491ac70637baf08de9c5aa8cfc6914772388d93ee05c21db80a00  SourceCurrentConjunctionAllocatedScanSoundness.lean
569ada204816c67d33cbbd87195e8ee45230219e0e3d185cdaefe8060f6877a5  SourceCurrentConjunctionAllocatedClassEntry.lean
d774c761a0345ce2d26a5eb8ed313dadd634d6747d5148267894bd80bcf29cc4  SourceCurrentConjunctionClassScanSoundness.lean
b5fe7c3c9cb143f63f4294c7696a18478846a35d12c5058eabf6d13e10d9f427  SourceCurrentConjunctionClassScanCompletion.lean
```

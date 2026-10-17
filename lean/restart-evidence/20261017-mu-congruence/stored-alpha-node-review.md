# Stored alpha node reconstruction review

The module has three public declarations. `RowsAlpha` is a pure relation
on original stored rows and two replacement environments. Rows match by
occurrence in both directions. Each match keeps the exact symbol and full
guard. Children use `ManyAlpha` with empty initial local scopes and values.
The relation has no execution equation or desired result premise.

`encode_rows` derives `RowsEquivalent` for the complete encoded edge lists.
The source heap supplies coherence and available independent leaf contexts.
Coverage relates each original row's leaves to its own source context.
The proof applies the distinct-child stored alpha-plan theorem. It retains
row occurrence membership without row order or multiplicity requirements.

`complete` takes two available open stored node roots, initial `Ready`,
available replacement environments, and the pure `RowsAlpha` premise.
The open premises select actual row reconstruction rather than closed-root
capture. Each encoded context is the corresponding root's own leaf list.
The node-plan initial producer constructs both sequential executions with
one identical complete Value. Each exact return retains `Keeps`, including
open-depth observations. The common returned value is available finally.
No caller supplies an actual return, future heap, future relation, or Cap.

Arbitrary nested Mu children remain allowed where the pure ordered alpha
relation is supplied. This module does not derive that relation from an
actual retained Mu writer. It does not permute union alternatives: union
children retain the alpha-plan relation's ordered member condition.

The no-premise integration constructs two distinct open ordinary roots
from actual source execution under two available bare-reference captures.
It derives semantic data, coverage, open depth, and both availabilities.
Each root has a literal false-guard row and a different original free name.
Two replacement maps resolve those names to the same available Depth
reference. The fixture proves pure row alpha and obtains the two actual
sequential repaired calls with one exact value and both `Keeps` receipts.
It also proves that the original roots are distinct and open.

Selected strict2 is empty. Canonical1 passes 558 jobs. Public1 checks three
full signature/proof/axiom pairs. Kernels3 checks one constructed pair.
All eight printer options are explicit. Selected proofs use only standard
axioms. All jobs report 4GiB memory.max, 4GiB memory.high, and zero swap.
Failed strict1 and kernels1/2 remain unchanged. The failures concern proof
unfolding and ground inequality proof syntax, not a changed theorem scope.
The owned peaks file snapshots the shared append-only file. The manifest
does not freeze that mutable shared path.

The initial same-value node bridge is complete. The general retained-Mu
writer-to-alpha producer and general recursive normalization fusion remain
separate obligations.

# Indexed producer paths and actual enclosing pending calls

Updated: 2026-10-13 16:02 CEST.

`InternedOrdinaryProducerCalls.Inputs` strengthens the source-path invariant
from `notes-pending-producer-paths.md`. It uses the exact lexical input index.
The crossing-prefix length equals that index. Equal ordinary levels can
therefore occur at different indices without identifying their producers.
The invariant also retains the producer's actual ordinary callback equation:
it returns the same pending key and final cache as the closed execution.

`InternedPendingProducerCalls.closed_encounter` derives this invariant from
the actual stopped evaluator. Completed siblings and later cache effects
preserve earlier producer equations. An ordinary entry adds its own equation
only in the branch where that actual callback has returned pending. Depth
and fresh entries introduce no ordinary input. The proof supplies no assumed
callback correctness or input provenance.

`InternedPendingProducerDescent.closed_enclosing_pending` retains the same
joint-key `Site` and `Mismatch`. The current pair is still exactly the two
original ancestor records. The theorem selects an indexed live captured
ordinary input of that ancestor. Its `EnclosingAt` witness retains:

- The actual introducing producer and the source path into the ancestor.
- The exact environment suffix and a strictly shorter captured environment.
- The producer's completed Depth callback and its exact returned level.
- Its ordinary callback, pending at the original key and final state.
- The whole enclosing binder execution, pending at that same key and state.
- Absence of that key before the producer and at its ordinary-entry start.
- Cache growth from that start to the ancestor's source start.
- The impossibility of reverse cache growth from the ancestor's allocated
  state to the producer's ordinary-entry start.

The last property gives a strict order between these cache cuts. It does
not give a numeric rank decrease. The earlier completed ancestor copy from
`InternedPendingProducerReplay.earlier_ancestor` still applies through
`Inputs.paths`. The producer's ordinary callback has not completed, so this
result does not supply another complete pair for the producer itself.

`InternedProducerPathBoundary` checks a further limit. Its closed source is
an outer smart binder with a node body. That node has a nested raw binder
and an empty child. The nested binder reads the outer ordinary input. Its
complete record retains `Unint 0`, and the source path reaches that binder.
The outer producer nevertheless completes with the empty result. The empty
child removes the edge only after both children have run.

The fixture has all variables in lexical scope. Its source execution,
stored record, target liveness, and absent outer liveness are kernel checked.
It is not a pending counterexample. It disproves the step from a live target
on a producer path to liveness in the producer's returned value. A descent
argument must retain execution effects on such paths. A rank on the
returned value alone loses them.

General closed constructor no-pending remains open. The new exact enclosing
pending execution still needs a recursive joint-key mismatch at a smaller
measure. The current theorem does not assert that step.

Validation uses pinned Lean 4.34.1. The focused audit checks 9,317 theorem
dependencies and permits only `propext`, `Classical.choice`, and `Quot.sound`.
The log is `/tmp/mcfta-producer-calls-audit.log`.
All existing fixtures remain unchanged.

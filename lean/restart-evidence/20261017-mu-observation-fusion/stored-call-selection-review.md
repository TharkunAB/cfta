# Exact selection of warm stored calls

The module supplies three public theorems. `select` takes actual warm stored
calls at one common heap and a second source list with the same complete
Value membership. It constructs the second list's actual ordered warm calls
and a `Calls` graph from the common heap back to itself. The result lists have
the same complete Value membership. Determinism of actual stored execution
proves this membership result.

The generic selection and observation theorems require no `Ready`, validity,
availability, or new completion premise. Their input is an actual warm call
observation. They do not initialize an execution from arbitrary inputs.

`distinct` specializes selection to the literal `distinctNodes` operation.
It requires source `Facts` and available original values. Coherent resident
identity readback proves complete source-value membership retention. It does
not replace complete-value equality with a row-language or reference equality.

`observations` retains the selected calls and complete output membership.
It also derives the same finite open observations at every depth and every
fixed view. The observation result follows from complete list membership.
Neither this module nor that implication proves cross-view transport or
reconstruction across an earlier union normalization.

The final strict source is `stored-call-selection-direct-2.source.lean`.
Its log is empty. The canonical target passes 551 jobs. Public attempt 1
checks all three declarations with full signatures, proofs, and axiom output.
Constructed attempt 2 has one no-premise integration. It builds a source union
with a productive Mu, a bare ordinary reference, and an ordinary node. It
constructs the actual stored member calls and replays them at their actual
common returned heap. It reverses and doubles the original list to six calls,
then applies physical source deduplication to obtain three calls. Both graphs
are actual same-heap calls. Their result membership and all finite observations
agree with the original member outputs. The count of calls does not assert
that different source inputs always have different outputs.

All selected runs use Lean 4.34.1 with actual 4 GiB memory max, 4 GiB memory
high, and zero swap. All eight printer settings are explicit. All selected
axioms are standard. Source attempt 1 retains the checked core before the
observation wrapper. Failed fixture attempt 1 and its raw log remain intact.
It needed the explicit union shape to transport member availability. No
older source or frozen evidence file changed.

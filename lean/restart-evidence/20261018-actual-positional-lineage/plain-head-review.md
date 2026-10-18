# Actual accepted Head origins

The frozen production source is `SourceCurrentActualPlainHeadOrigins.lean`,
SHA256 `06ce94f53911c3fd6558098dc8d4418359b6f3b8097fff82a5110faef963b81a`.

## Checked result

`head` uses an actual completed Head graph, initial NativeOperationHeap.Good,
causal GuardHeap Plain, input availability, and the actual gate acceptance.
It derives causal GuardHeap at the returned heap, Keeps, output availability,
an ordinary result, and an empty effective own field for every returned row.

`shared_head` derives that same Head graph from a literal successful
SourceCurrentAllocatedSharedEditWorker.head equation. It retains the exact
returned heap in the full shared state. It assumes no Ready or invariant
at a future intermediate state.

`required` derives its RequireNode graph from an actual successful Required
worker equation. It derives the returned causal heap and empty effective
own fields. The initial Good supplies semantic and cost facts internally.
An identity Required call can return a recursive value; this theorem does
not assert that all Required results are ordinary.

`positive_ordinary` classifies an actual observed positive-own Required row.
The own accessor must return a nonempty list of physical class records.
If a recursive original passes its gate, this positive row is impossible.
Therefore the original is an ordinary node. The theorem retains an indexed
source row and its complete guard, symbol, and ordered arity. It does not
assume a returned-origin relation.

`reached_head` obtains current Good, availability, and causal GuardHeap
from an actual unfinished outer Reached prefix and its initial facts.
The actual Head graph and its acceptance remain explicit observations.
The theorem does not assert that every outer node-body dispatch calls Head.
It does not assume per-prefix Good or causal heap as additional premises.

## Predicate and execution boundaries

Causal GuardHeap Plain equates the stored Mu body and probe guard profiles.
It does not require each physical raw edge guard to be plain. No raw-edge
AnnotationHeap Plain, global Cap, NoDeep, whole-forest closure, or finite
ordinary source restriction is added.

The theorems verify completed Head or Required calls. They do not construct
a future successful call from an arbitrary open recursive input. Gate
acceptance remains an explicit premise or a conditional premise for a
recursive original. No universal recursive acceptance is claimed.

A full Edit below an exposed root still needs its actual row-origin proof.
A full Local, Parent, and outer-prefix positional composition is not proved
here. Native leaf queries can introduce their own rows. This component does
not classify every full Edit result directly.

## Constructed integration

The fixture builds a closed guarded raw Mu `mu(pair self self)` inside an
ordinary source row with positive equality field `[[0],[1]]`. It allocates
the positive and empty fields from original allocation history. That history
and source construction derive NativeOperationHeap.Good and availability.
Closed source construction derives the causal GuardHeap Plain.

The same fixture proves that raw-edge AnnotationHeap Plain is false. It
separately derives acceptance of the selected Mu from its actual plain body.
A literal shared Head run returns one ordinary row. The new shared_head
endpoint proves that row has an empty effective own field. No future graph,
returned state law, caller Good, or gate answer is supplied as a theorem
input. The fixture has no input premises.

The Mu has a nonempty pair exposure. The fixture does not assert a nonempty
finite-term language or a full outer return. It tests the shared Head
endpoint, not the outer-prefix endpoint or a complete class edit.

## Validation

Selected strict `plain-head-direct-2`: exit 0, actual zero-byte log.
Canonical `plain-head-canonical-1`: exit 0, 1832 jobs. Existing dependency
warnings were replayed by Lake; the new source strict log is empty.
Imported `plain-head-public-1` checks all five public declarations with
full signatures, proofs, and axioms. Constructed strict
`plain-head-kernels-2` has a zero-byte log. Its full probe is
`plain-head-kernels-public-1`, one theorem. All selected probes use the
eight explicit options and only the standard three axioms. All executions
record 4 GiB memory maximum/high and zero swap.

Direct attempt 1 used Constraints for physical own records; the corrected
physical type is List Record. Kernel attempt 1 had predicate-inference and
closed-goal tactic errors. Numbered sources and raw failure logs remain.
No older source or evidence file changed.

This proves no active-key exclusion, bound on fresh recursive requests,
all-child-1 impossibility, or general outer termination.

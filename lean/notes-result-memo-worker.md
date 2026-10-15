# Recursive source result-memo worker

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
This proof extends [the actual first-child receipts](notes-outer-worker-demands.md).
The production equality and interned constructor code is unchanged by this merge.

## Full physical keys

`SourceEqualityPartialConstraintKey` uses the ordered list of physical class
tries as the equality-constraint interner key. It ignores the path-set cache.
This matches the fields used by `Eq PathEClass`. Trie child lists represent
`IntMap.toAscList`; source readback requires valid ascending tries. Arbitrary
permuted child lists are not claimed to be source IntMap representations.
Constructive mutual equality supports kernel execution without native axioms.

`identify_live` proves that interning preserves validity and stores the exact
key. `identity_iff` proves both directions between stored identity equality
and ordered physical key equality. `identify_same` and `identify_idempotent`
retain trie equality and repeated-key allocation. Contradiction has a separate
`none` tag. Live empty constraints have an interned identity.

These are reconstructed identities in an explicit constraint table. Native
prefixes do not yet expose all production EqConstraints allocation events.
The model identity 0 is not asserted to be the source process identity 0.
A production bridge must relate these tables up to identity renaming and
preserve live physical payloads. Existing cache validity supports that work.
It does not prove that the actual unsafe global table satisfies the model.

## State and recursive execution

`SourceEqualityPartialMemoWorker.State` retains the full native state,
constraint interner, and typed result-thunk table. Requests retain both the
original inherited payload and complete immutable node record. The key is
`(Option constraintIdentity, NodeRef)`. NodeRef retains the source constructor
tag and interned node identity. The result cell retains a complete node value.

Preparation identifies the physical payload. Lookup publishes the original
suspended request before demand starts its body. A hit keeps that request.
A completed hit returns its stored node without running the body. A running
hit returns a distinct busy observation. `request_ready` and `request_busy`
prove these branches for every supplied body.

Indexed children and ordered rows pass all three state components to their
next request. Local edge narrowing reuses the existing concrete native worker.
Physical own readback, inherited combination, contradiction, trie descent,
original-label edge reconstruction, modifyNode, Mu reconstruction, unions,
and the source Rec error retain their source branches. Only successful node
results complete a cell. Errors and incomplete observations do not install
a successful result.

This is a sequential demand adapter. It is not a theorem that Haskell forces
all rows in this order. The prior necessary first-child proof applies to the
verified unfinished one-row bodies. GHC scheduling, native containers,
exception thunks, unsafe IO, and memory ordering remain separate boundaries.

A body bound limits new body evaluation. A completed hit needs no remaining
body bound. Publication and demand precede an exhausted-body observation.
That observation retains the current evaluating cells. Increasing a bound
requires a fresh execution from the original starting state. Resuming the
saved evaluating state would instead observe busy. Busy, source errors,
exhausted traversal, unfinished native stages, and pending constructors are
separate observations. None is a production fallback or repaired cycle policy.

## Actual closed cycle

`SourceEqualityOuterMemoWorkerCycle.observation` constructs the original
closed normalized R fixture with empty result and constraint tables. It runs
the recursive worker with body bound 2, native bounds `(4,4,2,2,2,1024)`, and
32-bit words. The worker executes both actual native prefixes. Its next
recursive demand finds the published root cell under evaluation.

`actual` checks this execution in the kernel. `actual_pending` retains the
full observation receipt, exactly two allocated running cells, their empty
inherited payloads, the distinct wrapper reference, and the original root key
and handle. `observation_receipts` derives the original construction and full
recursive execution equalities. No separate abstract request trace or supplied
successful callback is needed for this fixture.

No completed result is installed in either cell. This observation does not
prove GHC divergence or a particular exception. The retained Haskell source
certificate and cold/warm timeouts remain separate execution evidence.

## Completed-cell target status

The [completed-cell proof](notes-result-memo-soundness.md), `51a5922c`, closes
the bounded successful semantic preservation target below. It follows actual
recursive effects and derives warm ready reuse. A concrete successful cold
source fixture supplies its reached check plan. Constraint allocation up to
identity renaming and source demand/runtime correspondence remain open.
The next-target section below records the earlier worker checkpoint.

## Next proof target

Prove a completed-cell invariant for this worker. Retain the original request,
physical-key agreement, immutable resident result, and exact contextual
language under inherited satisfaction. Derive it through actual children,
rows, native effects, and successful completion. A warm ready hit must reuse
that proof under heap extension without re-executing native effects. Exact
native-state equality with a nonmemoized replay must not be assumed.

Then connect completed executions to the existing caller graphs and language
laws. Preserve the actual busy counterexample and separate source runtime
boundaries. General caller completion, open contexts, repeated fixed points,
getAllAtPath, decision-model, and extraction remain open.

Focused kernel build: `/tmp/mcfta-outer-memo-worker-cycle-20261015.log`.
Aggregate axiom audit: `/tmp/mcfta-result-memo-audit-20261015.log`.

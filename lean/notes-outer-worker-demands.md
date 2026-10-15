# First-child demand from the actual outer worker

Source: `TharkunAB/cfta`, main `239feb64`. This work follows
[the closed caller cycle](notes-outer-caller-cycle.md). It changes no Haskell
source. Existing source builds, counterexamples, and proofs remain intact.

## Actual worker receipts

`SourceEqualityOuterCallerWorkerCycle.observation` constructs the original
closed normalized R fixture. It runs `SourceEqualityPartialWorker.run` with
outer bound 1 and native stage bounds `(4,4,2,2,2,1024)`, at 32-bit words.
The first incomplete result is the recursive request for W(R). The observation
retains that exact callee, inherited payload, and full native state.
It then runs the same one-level outer worker at W(R), with those actual
arguments. The next incomplete callee has R's original physical node reference.
Both inherited payloads have the literal empty physical constructor.

The observation stores both returned native states. `observation_receipts`
derives the original construction equality and both complete worker-result
equalities by case analysis of the actual execution. No completed caller
graph, future warm scope, or successful recursive callback is supplied.
The computed observation also checks that R and W(R) are distinct ordinary
nodes with one row each. `actual_cycle` checks these facts in the kernel.

The one-level observation is an exhausted recursive call, not a successful
parent return or a claim that every traversal bound is insufficient.

## A required first child for every callback

`SourceEqualityPartialFirstDemand.first_required` is a general one-row law.
It takes the actual one-level incomplete-child receipt. For any replacement
recursive callback, a successful parent step requires a successful result
from that same first callee at that same warm state.

The proof follows the actual ordinary branch, single row, guarded native
prefix, physical own accessor, combination, and indexed child walk.
The observed live child excludes accessor errors, contradiction, empty child
forests, and unfinished native stages. A callback error or incomplete result
cannot produce a successful parent. No termination premise for the parent
or child is used to establish this necessary condition.

`SourceEqualityOuterCallerWorkerCycle.required` instantiates this law at both
actual fixture callers. `actual_pending` combines their full receipts and
necessary first-child conditions with the existing typed result-thunk trace.
The trace publishes both distinct empty-inherited requests before completion.
The repeated root lookup keeps its original handle and demand observes busy.
Neither result is in the completed projection. Busy remains a logical
observation, not a source return, fallback policy, or specified GHC exception.

## Haskell strictness comparison

For the verified unfinished one-row bodies, the source has this demand chain:

1. `modifyNode` compares the rebuilt row list with its original nonempty list.
   Edge equality reads the first rebuilt edge's identity.
2. Equal-arity `setChildren` interns the edge. Its length test evaluates the
   entire finite child-list spine. It does not evaluate child result values.
3. Edge interning computes the key hash, including on a cache hit. The child
   list hash forces child node hashes.
4. A node hash reads its constructor and canonical identity. It does not
   require every descendant's normal form.

The live combined payload matters. Contradiction maps each child to EmptyNode
and skips recursive callbacks. Positive arity matters. A finished memo hit
can also return immediately. The necessary demand concerns an unfinished body.
It does not imply eager evaluation of all outer rows or row tails.

The source locations are `Equality/Operations.hs:79-95,127-130`,
`Interned/Type.hs:209-210,321-330,395-400,499-508,620-627`, and
`Interned/Cache.hs:111-115,169-180`. The cached hashable 1.5.1.0 source uses
`SP !Int !Int` and a strict list fold at `Data/Hashable/Class.hs:566-576`.
Its `Hashed` value has a strict cached hash at lines 863-867.
The local archive is
`/home/tritlo/.cabal/packages/hackage.haskell.org/hashable/1.5.1.0/hashable-1.5.1.0.tar.gz`,
SHA-256 `ed0b7c10ce92c9ffe45420dadc38c6d39db486ff3633ff13567cc9f75f79b112`.
The exact excerpts are in `/tmp/mcfta-worker-demand-source-audit-20261015.txt`.
This is a source comparison. It is not a proof of GHC execution or blackholes.

## Validation and remaining work

Both new modules pass focused builds. The aggregate audit passes 1,894 jobs
and checks 49,138 theorem dependencies. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. The older unused `inputs` warning remains.
Logs are `/tmp/mcfta-outer-worker-cycle-20261015.log` and
`/tmp/mcfta-outer-worker-cycle-audit-20261015.log`.
No Haskell source, reproduction, package file, or toolchain setting changed.
Earlier Nix Haskell, benchmark, formatting, and metadata checks were not
repeated. These component checks do not prove whole-library correspondence.

Next integrate the actual result memo with the recursive worker. Represent
its full source key: inherited EqConstraints identity and node identity.
Retain the source trie-based equality of interned equality-class keys;
semantic equality of denotations is insufficient. Thread publication,
running cells, completion, and memo state through actual child, row, and
native-state effects. Preserve busy, source errors, and exhausted bounds
as distinct observations. Compare completed executions with the existing
caller graph and language theorems. A demand on an unfinished cell is not
a production cycle policy. Keep Haskell runtime correspondence explicit.

General caller completion, open contexts, repeated fixed points,
getAllAtPath, native containers, GHC scheduling, decision-model, and extraction
remain open. Preserve Sized exact classes, finite size execution, size order,
both distinct rank inverse contracts, and the optimized interned core.

# Fixed-own growth and actual outer calls

Read-only review at 2026-10-18 03:34 CEST. The reviewed checkout is
`9c3442e54953d24935399ac7ec66868d4b66b8ca`.
This review adds no production theorem or runtime counterexample.

## Exact gap in the algebraic example

`SourceEqualityInheritedGrowthBoundary.raw` uses classes
`{0,100}` and `{01,101}`. Its `walk` combines the same own field at every
step and always descends through child 1. Its checked finite prefix has
heights 0,3,4,5,6. Its statement expressly omits actual outer reachability.
See `lean/MicroCFTA/SourceEqualityInheritedGrowthBoundary.lean:31-51` and
`:80-99`. No new recurrence or height computation is added here.

The normalized own field also contains congruence extension `1001` in the
second class. Its complete path footprint is
`{0,100,01,1001,101}`. All paths through child 1 start with `10`. None ends
at `1`, and none enters `11`. Executable diagnostic `fixed-own-footprint-3`
returns exactly
`normalized [[[0],[1,0,0]],[[0,1],[1,0,0,1],[1,0,1]]]`.
It evaluates the reference normalizer at bound 32. It is not a kernel theorem
or a public proof pair, and it does not test an outer execution.
Proof attempts 1 and 2 were interrupted with wrapper exit code -15
(SIGTERM), before any proof output. Their immutable sources, empty raw logs,
metadata and 4 GiB/4 GiB/zero-swap readbacks remain present. No final peak
was recorded for those interruptions. Attempt 3 passes at 118 MiB under the
same limits. No interrupted attempt is reported as a theorem failure or
success. No production module was changed.

The algebra does not supply the missing next positive-own row. Actual
`reducePartially'` first calls `reduceEdgeIntersection`, then recurses into
the returned children with the combined and descended inherited payload.
See `cfta/src/Data/CFTA/Equality/Operations.hs:80-96` and `:143-168`.
Thus one must justify both the constraint transition and the returned row
that can repeat it.

## Concrete source constraint on the all-1 route

For this exact footprint, class edits at child 1 are below child 0. The
compiled edit at child 1 is `EditBelow`, never `EditAt`. After its ordinary
root is exposed, its child 1 is unselected. `editAll` can install a native
intersection result only at an `EditAt` leaf. Its `EditBelow` branch keeps
the row field and edits the named children. See
`cfta/src/Data/CFTA/Equality/Operations.hs:305-334`.
`requireAll` has the same branch restriction: the needed entry at child 1
selects child 0. It can remove rows with insufficient arity and rebuild
surviving rows, but it does not narrow their child 1. See `:283-302`.
A contradiction or Empty propagation can end the route instead.

The formal source graphs retain these distinctions.
`SourceCurrentAllocatedSharedEditGraph.EditNode` separates leaf replacement,
ordinary reconstruction, and recursive Head exposure at lines 31-45.
Its `EditChildren.unselected` returns the exact input child at lines 47-59.
`SharedEditRowLineage.children_indexed`, lines 29-35, exposes this identity
at the actual selected index. Its `rows_indexed` retains the source row,
ordered child call, full field, and captured states. Required ordinary
rows retain their full fields by
`SourceCurrentRequiredGuardOrigins.ordinary`, lines 75-95.

Thus merely assigning the field to a plain recursive `tau` does not
justify a repeated positive-own event. A gate-accepted recursive source
region has hereditary plain annotations. `SourceCurrentGatePlainRegion.annotations`,
lines 52-58, and `reached_empty`, lines 73-81, establish this fact on reached
stored source rows. The actual reconstructed Head needs a further local
causal transport proof. `SourceCurrentRequiredGuardOrigins.accepted_head`,
lines 139-151, has a `GuardHeap Plain` premise. That premise must not be
assumed for a mixed heap that also stores the positive guard. This review
does not silently use that theorem as a general Head producer.
A constrained Mu crossed by the selected paths instead refuses the class.
See `Operations.hs:213`, `:255-270`. If no selected class exposes it, the
outer worker returns that Mu unchanged at `:84-86`.

This source inspection suggests a specific missing lemma. Through actual
Required and class-pass reads for the exact footprint above, every surviving
positive row reached by repeated child-1 dispatch should retain a proper
preexisting ordinary child-1 row occurrence, or originate in an actual
recursive exposure separately proved plain from causal history. In the ordinary case, it should retain the exact
next child-1 value at the corresponding row index. Canonical row filtering
and reordering require occurrence witnesses; physical index preservation or
injectivity must not be assumed. Iteration would then bound consecutive
positive all-1 steps by the finite initial ordinary right-spine occurrences,
with plain exposure unable to add a new positive step.

This is a proof route, not an established theorem. This review does not
prove that the all-1 algebraic sequence is unrealizable. Finite initial
ordinary chains can already contain repeated equal guards. The exact
footprint lemma alone does not supply the required call/occurrence mapping.
The new root row-field theorem identifies immediate captured source rows,
not proper occurrences in the initial recursive source. See
`SourceCurrentOuterRowFieldOrigins.lean:285-288`, `:451-454`, and `:509-543`.

## Why OriginalRepeat does not settle this route

`SourceCurrentOuterOriginalRepeat` uses a different own class,
`{00,01,1}`. It includes an edit endpoint at child 1. Its actual Parent
return has children `[original,child]`, although `original` was the active
outer input. See lines 42-68. Its next request selects child 0, not the
all-1 route. It carries inherited class `{0,1}` and a different complete
memo key. Combining that inherited class with the repeated own field is
contradictory. The actual repeated call and root call both return Empty.
See lines 116-128 and 154-162.

This proves that complete values and physical row identities can repeat.
It refutes whole-value strict descent. It does not refute a proper
contributing-row occurrence argument, and it is not a busy-key loop.
The physical key is the inherited identity paired with the tagged node
reference, not the own field or its path height. See
`SourceCurrentAllocatedPartialState.lean:27-49`.

## Remaining global obligation

The exact all-1 footprint may isolate a useful necessary restriction. General
recursive traces can change child index and can copy positive rows into
other branches. The path `100` is an actual potential destination of the
fixed own class. Such a route includes extra descents that the pure walk
through child 1 omits. This review does not supply a measure for those
mixed-index routes. Retained-Mu writer alignment is also separate.

The next general result still needs an occurrence-sensitive transition
through actual Required, class edits and native writers, followed by
compatibility with every active physical key. Even all-owner key separation
would not bound the number of fresh requests. No actual infinite outer
trace, Haskell defect, global finite inheritance carrier, or general
termination theorem follows from this review.

## Source pins

- `cfta/src/Data/CFTA/Equality/Operations.hs`:
  `5bf6e9b0f4033c11ac7723a17fe8d1b94d95a259187f0402285ad0147e439b09`
- `lean/MicroCFTA/SourceEqualityInheritedGrowthBoundary.lean`:
  `f087ea1af7b4736f3293addc48cd3b5b0b016903780206e3a3995b213e22f450`
- `lean/MicroCFTA/SourceCurrentOuterOriginalRepeat.lean`:
  `6e1886f859f625bb013ac74e9a47016833bbe9678ea42e2ab62739ebd1847da3`
- `lean/MicroCFTA/SourceCurrentSharedEditRowLineage.lean`:
  `4b02b1748d11f0e5eb19cdd1f4da1f7dd44cfb7164a77c509b560b01d347d28c`
- `lean/MicroCFTA/SourceCurrentGatePlainRegion.lean`:
  `aa76a1b61f6b5b9e9a3f6c5c84b627ea7602b37e3e6257ce9b0a5d7f3cd664c0`
- `lean/MicroCFTA/SourceCurrentOuterRowFieldOrigins.lean`:
  `6fd6ea71912533f1c3900f9ffa5677cfb48aaa490c1ebde16b741b578e20fa80`

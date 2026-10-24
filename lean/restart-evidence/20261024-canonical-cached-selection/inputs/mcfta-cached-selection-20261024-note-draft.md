# Canonical cached selection and actual union transfer

The current Haskell selector reads its cached candidate set and canonical
waiting keys. It performs no representative lookup or path compression.
The new model follows that source operation. Earlier raw-count and resolving
index models remain unchanged.

## Checked interfaces

`SourceUnionFindRoot.root` follows parent entries without constructing a
replacement forest. At every finite bound, it equals the representative
projection of the existing compressing lookup. Every successful result has
an actual finite path. Every finite path supplies a sufficient bound.
The explicit bound exposes execution. It is not an additional Haskell result.

`EnumerationCanonicalWaiting.Correct` counts suspended references after it
maps their variable IDs through a supplied representative function. This is
a ghost count view. The executed value slots, tries and fragment IDs remain
unchanged. Counts retain duplicate references. Stored key support is exact.

Initialization, allocation and valid replacement preserve those equations.
Completed assimilation moves the source reference list into the target and
eliminates the source. The waiting table stays unchanged. The invariant is
proved at the completed endpoint, rather than between the two writes.
`EnumerationPureSelection.assimilate_source` connects the live pending-slot
branch to that endpoint, including its complete modeled core and ancestry.

`EnumerationPureSelection.find` returns none when there are no candidates.
It returns some empty list when candidates exist but all are blocked. Otherwise
it returns the ready IDs in increasing order. `next` uses the existing valid
preference and minimum fallback rule. `candidates_exact` identifies the full
candidate list used by the stop test before waiting keys are subtracted.
The CPS action returns one result with the complete cached state unchanged.

`scan_agrees` requires correct canonical indexes and actual representative
paths for the supplied root function. Every successful old scan returns the
same selection. Its actual final state satisfies the complete compression
frame. The frame keeps the counter, slots, obligations and both ancestry
fields. It preserves every finite root path, including the root ID and size.
`scan_complete` obtains a sufficient finite old-scan execution. Neither
statement asserts equal final forests or success at every finite bound.

## Actual union endpoint

The union-transfer theorem consumes the same actual union-loop execution and
final representative read. It derives the final root map from the existing
exact joined-class invariant. It then relates the count-transfer fold to that
map and the actual final forest. Its key contract is the source set of old
representatives with the final winner removed. It permits that set's actual
iteration order. It does not assume the desired final root map.

This interface starts after the old representatives have been recorded.
It constructs the cached endpoint over the same returned core. The temporary
state after a forest union and before its count transfer need not satisfy the
canonical index invariant. The theorem does not require that intermediate
invariant. Connecting the pre-scan and every later native delta update into
one maintained source-history invariant remains separate work.

## Remaining correspondence

Selection equality and a compression frame are insufficient for arbitrary
callbacks. A callback can inspect a raw parent pointer, leave state unchanged,
and return a different decision after compression. Thus ReadOnly alone does
not give observation preservation. The actual public observing operations
need relational proofs before the shared drivers can be related.

The same finite bound is also insufficient across related forests of different
path depths. Future driver correspondence needs sufficient bounds or an
explicit bound adjustment. The frame does preserve actual root sizes, which
matter when union selects its winning representative.

Other gaps remain: full canonical mutation-history composition, native delta
and container realization, canonical aggregate machine-integer bounds, both
recursive outer views, shallow preparation and narrowing preservation, and
the new phase-4 typing, pruning, runtime and parallel correspondence.
Partial outputs can contain holes with no accepted completion.

H6 `SourceCurrentColdFiniteWarmCalls.constructed_node_calls` remains the
strongest combined execution and finite-tree language theorem under its
existing premises and formal guard interpretation. Full-pipeline composition,
upper resources, practical machine width, solver correspondence and general
convergence remain open. The full goal remains active.

No Haskell source change or new Haskell repair is part of this checkpoint.
FINDINGS retains the external repair index first. The negative-depth fix is
merged in PR #168. Both optional LPO defects remain open.

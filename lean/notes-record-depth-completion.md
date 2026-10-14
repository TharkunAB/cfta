# Source completion with arbitrary captured records

Updated: 2026-10-14 11:49 CEST. Proof checkpoint: `e4a011e8`.

## Exact input observations

`InternedRecordDepthShape.shape` decodes each actual record. References supply
root alternatives. Nodes and Mu values supply opaque alternatives with their
actual free names below the constructor. Unions retain the ordered component
shapes and the actual cached depth. Thus a mixed opaque union retains its
literal root alternatives. An opaque root profile alone is insufficient.

The shape has the exact cached depth, root profile, and deep-name membership.
Available coherent records also have the exact decoded free-name membership.
Normalized available records supply the complete `Observed` condition.
These facts are derived from the records; callers supply no shape relation.

`InternedRecordDepthSource` connects the decoded inputs to the existing
independent source profile and free-name proofs. It derives exact returned
emptiness and the deep names of an ordinary source root.

## Full source execution

`InternedRecordDepthCallback` evaluates each body with a distinct symbolic
local. Substitution supplies the actual reference argument and retains every
captured record's shape. Actual callback normalization preserves depth and
deep names. Away from the supplied argument, actual free names are exactly
the symbolic fixed captures.

`InternedRecordDepthExecution.build_depth`, `buildMany_depth`, and
`buildEdges_depth` prove the complete syntax induction. Every outcome retains
the decoded depth heap. Returned values have exact interpreted emptiness,
cached depth, and deep-name membership. The binder case proves all actual
callback observations and applies `DepthRequest.request_checked`.
`DepthComposition.binder_shape` derives decoded binder observations for any
symbolic body shape. The old literal APIs retain their statements and now
specialize these general results.

## Successful source construction

`InternedRecordDepthLevels.project` retains ordinary names and maps other
reference kinds to Depth inside each decoded shape. Equal projected inputs
give equal actual Depth-callback depths and ordinary free-name bounds.
Therefore the repaired ordinary levels agree. A varying reference prefix
with the same fixed captured records satisfies this relation when its
projected names agree.

`InternedRecordDepthRoutes.Path.projected_names` follows the actual current
path from outer crossings to inner crossings. The earlier route retains its
exact captured suffixes. The projected inputs and chosen ordinary levels
agree at each crossing. This does not assume callback depth or level replay.

`InternedRecordDepthCompletion.site_impossible` contradicts the ordinary
mismatch required by an actual pending encounter. Actual growth recovers the
decoded heap at every earlier callback start. `source_not_pending` derives
the final heap through actual execution. `source_complete` returns the actual
successful value and final cache for arbitrary syntax and captured records.
Its initial premises are `Context`, `DepthHeap.Heap`, and `Covered []`.
No prepared-body or supplied constructor-termination premise is used.

## Actual optional binders

`SourceRecursiveIntersectionMaybeMuCompletion` uses the exact existing
`maybeMu_eq` equation. Available stored leaves supply the lexical context.
`semantic_context` preserves the original lexical inputs and all semantic
heaps. `not_pending` excludes unfinished optional binders. `complete_decoded`
derives the successful value and exact cache, retained context and decoded
heap, complete coverage, result availability, growth, and issued history.
The stored body can contain arbitrary available captured Mu records.

## Remaining native obligations

Derive the full semantic context and decoded depth heap through actual native
prefixes. Follow actual emitted work and its available inputs. Arbitrary
`Work` instructions can install invalid records. Complete coverage alone
does not establish these semantic invariants. Apply `MaybeMu.not_pending`
at the exact reached constructor site, then strengthen finite native
return-or-pending to successful first-run bounds.

Output preparation, or a broader cold-reader invariant, and physical product
row membership and rejection remain open. Universal preparation preservation
at reached bodies remains refuted. The separate shorter-producer descent
remains unclosed and is not needed for these source completion results.
Keep its checked histories and counterexamples.

## Validation

Lean 4.34.1 passes 1,340 aggregate jobs and 42,373 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-maybe-mu-completion-20261014-audit.log`.
No Haskell source changed. The prior 641 passing Nix examples and active
package formatter checks remain the source validation checkpoint.

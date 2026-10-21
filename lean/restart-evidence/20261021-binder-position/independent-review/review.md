# Independent mathematical review

Reviewed on 2026-10-21 at 02:44 CEST. The complete 506-line candidate is
`SourceCurrentBinderFreePublicationPositions.lean`, SHA256
`c6b0fa14dfda117cc4c3e05a6a7ba36c070ee96c3ef4013cc792e4f9535d7a45`.
No material issue was found. This review owns zero Lean/Lake commands and zero
public proof pairs. It reuses one complete selected public readback.

## Exact contract

The sole public theorem, `publication` (line 488), takes one actual
`NativeMuPublication.Publication`, `BinderFree event.expression` and a finite
natural child path. It derives `PositiveAt event.body path` if and only if
`PositiveAt event.ordinary path`. The same event supplies the source expression,
fixed capture list, actual Depth and ordinary callbacks, fresh reservation,
actual body callback and initial rich Context. There is no supplied positive
position correspondence, Plain-capture condition, future return or desired
callback output.

BinderFree excludes binder syntax recursively through node children and union
members (`InternedStoredShallowCompletion.lean:20`). It does not exclude Mu
values in the actual captures. `PositiveAt` follows ordinary child positions
and literal union alternatives. It does not enter a Mu body or follow a
reference (`SourceCurrentRequiredPositivePosition.lean:26`). This is a theorem
about those finite opaque-barrier positions, not about observational unfolding.

## Simultaneous relation and induction

The private `Same` relation (line 198) retains both the exact Empty-reference
Boolean and positive-position equivalence. The Empty fact is necessary: node
normalization discards a row if any child is Empty. Positive-position equivalence
alone would not preserve that test. `RowSame` also retains the complete guard
and an ordered All2 child relation. `all_lookup`, `dead_same`, singleton and
surviving-row lemmas preserve the exact natural child index. Row choice is
existential in PositiveAt, so canonical row ordering need not be equated.

The mutual build/many/edges proof (lines 341-457) follows actual successful
subcalls in source order. Empty is immediate. Variable lookup uses the SAME
index and handles the out-of-range Empty default. The binder case contradicts
BinderFree. Node and union cases derive actual intermediate Normal and
availability facts before constructor readback. Ordered children and tails
retain their lexical input values across actual intermediate heaps. No pending
execution is treated as a completed subcall.

The build relation is instantiated with identical captures. Only the local
reference names differ. Each local reference is nonempty and has no PositiveAt
constructor, so its simultaneous relation is derived directly. There is no
reference resolution or capture payload substitution in that step.

## Actual warm constructor readback

`makeNode_positive` (line 79) uses the actual full canonical node-edge readback
from `EqualityLeafProjectionPhysical.makeNode_edges`. The proof uses coherence,
linked records and full resident rows to retain membership after canonical
ordering and duplicate removal. Its Empty test uses the existing exact
normalization theorem. It does not assume a cold node table.

`makeUnion_positive` (line 137) follows actual flattening, first-identity
selection, singleton return, mixed stored-union readback and ordinary-edge
collapse. Full resident-value retention justifies deduplication, including warm
union record readback. Live/Normal facts justify removal of dead ordinary rows.
`node_same` and `union_same` combine these positional facts with exact Empty
characterizations. The ordered edge proof uses complete requested child-list
readback from `InternedShallowValues.makeEdge_children` and the full requested
guard from actual coherent edge allocation. It does not identify arbitrary
same-key payloads without those physical invariants.

## Filter and final callback correlation

`filter_positive` (line 175) follows `withoutSelfReference`. Non-union values
pass through. The deleting union branch removes only a bare reference equal to
the selected local name. The theorem `referenceOf_self_iff` makes that equality
literal, and a bare reference cannot carry PositiveAt. The actual normalized
makeUnion preserves the remaining positive positions. The proof does not claim
that arbitrary local-reference filtering preserves Empty; it needs only the
positional law after the final callback filter.

`callback_positions` (line 461) compares the actual raw builds, then their actual
final filters. The public theorem derives the ordinary callback Context from
the SAME Depth callback, then the cut Context from the SAME ordinary callback.
It reserves that event's exact key and derives the available local reference.
It compares the body callback at event.allocated with the ordinary callback at
event.afterDepth, using the SAME event.environment and actual bodyDone and
ordinaryDone. No heap or callback is reselected.

## Limits and readback

The theorem relates this event's callback body and ordinary probe. It does not
assert equality of full values, row indices, symbols, heaps, source syntax, or
language. It does not by itself identify a selected keepFirst winner with this
candidate's body; a consumer must retain the actual selected publication. It
does not prove a law for nested binder syntax, native intersection outputs,
global cache support, source rank or outer completion. Arbitrary captured Mu
values remain opaque throughout.

Selected stems are `binder-position-direct-4` and `binder-position-public-1`.
The strict log is literally empty and matches the frozen source. The 68,269-byte
public log contains complete check, full proof and axiom readbacks, all eight
printer settings, no omissions, and only standard axioms. Both receipts have
terminal zero, effective 4 GiB max/high, zero swap, a five-minute cap and fresh
usage above one percent. Original recorded commands remain unchanged. The
owner selection records five commands and three failed earlier elaborations;
this review reruns none of them. Portable verification checks snapshots;
--live also checks ROOT-relative foundations and the installed candidate.

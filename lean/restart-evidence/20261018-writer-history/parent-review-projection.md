# Independent positive projection source-route review

Reviewed at 2026-10-18 23:43 CEST. I read the complete final
SourceCurrentPositiveProjectionSourceRoute source, SHA256
37141d118ba5ebaae46d063873a687d0bb825123d274d43355c0ca9b96fac1d0.
I found no material issue. This review starts no Lean process. It reuses
three fully printed public declarations and adds no proof or fixture.

The public positive theorem requires an actual historical NodeTrace with
answer false. It does not replace this trace with a predicate about a
prospective call. PrimaryReplay.node_replay places the same false trace at
the later projection entry through Grows. The theorem separately requires
SemanticReady and Available at that entry. It does not infer issuance or
current availability from returned-record retention alone.

The historical UnionNormal premise has a specific use. The finite primary
shortcut tests cached depth zero and an empty free-name list. Those fields
alone do not exclude a union of ordinary nodes. RequiredFiniteExposure uses
the historical UnionNormal invariant to exclude that unreduced union. The
proof then follows original ordinary children using their historical
availability, cached depth and cached free-name equations. It does not
transport UnionNormal backward from the current heap. SemanticReady alone
does not supply this separate invariant.

A false primary trace cannot select a reference, union or gate-rejected Mu.
For a gate-accepted Mu, GatePlainRegion.annotations derives hereditary
Plain annotations from the historical available source value. This visits
the stored body and its source children. It does not assume that unrelated
heap rows or the probe values are Plain. ConstrainedCapOpenExposure.head
and nodeEdges preserve these annotations through actual recursive exposure
at the current heap. Each such row contradicts the selected row's explicit
non-Plain premise. Thus a selected non-Plain row cannot originate from the
recursive Head case under the stated assumptions.

The current Guards premise is ConstrainedCapGuardHeap.Heap Plain. It states
equality of the stored body and ordinary probe guard profiles for each
resident Mu. It does not require every ordinary row in the heap to be
Plain. The argument therefore allows the positive ordinary rows for which
the route is useful. This certificate remains an explicit current-entry
assumption. The theorem does not derive it from physical Good alone.

The proof threads actual read and projection effects through the ordered
workers. It uses the guard certificate at each actual intermediate heap.
The private Accepted law quantifies later reads with their own physical
support. It does not silently rebase a read graph to another heap. In a
union result, makeNode_edges and canonicalEdges_member recover a surviving
complete row from the actual read list. The proof does not substitute an
arbitrary resident row or a row with only matching symbol and arity.

Route records an exact natural row occurrence at every ordinary node and
the literal signed child selection for each path component. Its endpoint
is the same complete physical row as the selected result row. The public
positive theorem uses natural paths mapped through Int.ofNat. Positivity
here means that SourceMemoGate.plain is false. It can include residual
opaque guards; it is not restricted to a nonempty stored own field.

Route.mass_lt proves that each child of the retained endpoint row has
smaller InternedValueMass than the projection operand. The route contains
only ordinary source-child steps. The operand can already be a result of
an earlier edit or native product. Neither theorem identifies that operand
with the initial outer input, proves a decreasing next-call anchor, bounds
equality renewal, excludes active node keys, proves general termination,
or establishes Haskell correspondence.

Selected receipts are projection-direct-3, projection-canonical-1 and
projection-public-1. The direct snapshot exactly matches production and
its log has zero bytes. Canonical one completed all 1138 jobs. Its only
warning is the existing InternedFreshOrdinaryClosedCompletion unused-input
warning. The public group passes the existing hardened checker for all
three full signature/proof/axiom pairs, all eight printer settings, no
printer omissions and only standard axioms. All three runs record a
4294967296-byte memory maximum and high limit, zero swap, and the five-minute
capped runner command. The separate pins file contains only this report,
reviewed source dependencies, the checker and the selected immutable
receipt files. It excludes mutable fixtures, peaks and shared selections.
The frozen parent component is unchanged.

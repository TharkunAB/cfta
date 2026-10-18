# Actual outer scheduling and native lineage review

Recorded 2026-10-18 04:45 CEST. This is a source review with one checked
source-construction witness. No new production theorem, general termination
theorem, or Haskell defect is claimed.

## Exact outer handoff

AllocatedPartialWorker.rows first completes edgeCall on an original row.
It then enters descendants on the returned Parent edge before the next
original row. descendants combines that returned edge's actual full field
with the inherited value. A contradiction erases children. A live result
enters walk at index 0. At a reached walk index f, its exact next node
request is the pair of actual descend(combined,f) and returned.children[f].
Earlier siblings complete before the walk reaches this slot. See
SourceCurrentAllocatedPartialWorker.lean:119 and :134 and :158.

Suppose this child is an ordinary node with a positive row whose child c
is next. The worker does not immediately recurse on next. nodeCall first
demands its own result cell. A ready hit returns without entering rows.
Busy remains a failure. An evaluation enters the captured owner's body.
An ordinary body enters its rows. That selected row has its own edgeCall,
Parent return, inherited prefix, and ordered child walk. Only this second
walk can pass next, or its actual narrowed replacement, to a node request.
Empty, union, and Mu bodies do not enter that outer ordinary-row schedule.
See AllocatedPartialWorker.lean:61 and :74. KeyIdentity.node_evaluate_owner
identifies the complete captured request only with its stated Sound,
EqReady, coherent, and Available premises; malformed tables are not covered.

The index handoff is exact: row.children[c] becomes forest slot c in its
Parent call. Thus an initial (f,c) footprint becomes a required (c,c)
footprint at the next stage. In particular fixed (1,1) is positionally
compatible. This review found no index-renumbering counterexample to that
fixed-index schedule. It does not establish that a given execution reaches
all intervening successful calls or supplies the next row's footprint.

A footprint is attached to the guard on the row being reduced. It is not
hereditary over guards in its children. For example, a plain enclosing row
has an empty own-class footprint. Its ordinary child can have a row with
own class [0]=[1]. That child row fails Unselected(1,1), because [1] is an
ancestor of [1,1]. The focused source-built witness checks this
exact footprint failure with a complete coherent record. It is not an outer
execution counterexample. An enclosing footprint alone cannot supply
the next Parent footprint. Full raw-field origins can transport a footprint
when the actual contributing original field has that same property.

PositionalOriginChain.Below uses the previous selected continuation as the
next anchor. Its mass decrease and well-foundedness are valid for that
relation. The worker can reconstruct the containing node without invalidating
that local decrease. The separate missing producer must associate the
actual consecutive active operations with Below, including their real index,
positive own field, Link, completed earlier prefixes, and full physical keys.
A supplied chain premise is not that producer. Mixed indexes, plain rows,
terminal branches, and sibling work remain outside a fixed-positive-chain
termination conclusion. See PositionalOriginChain.lean:21.

## Native request and optional binder boundary

Native compileEdge preserves child order through zip and requests each
operand pair at that index before makeEdge. A surviving ordinary native row
has full symbol, joined raw guard, and an exact historical child request.
NativeNodeRowLineage.Lineage retains the resulting child value and that
actual call. It does not identify the result with either operand child.
See SourceRecursiveIntersectionCompile.lean:45 and
SourceCurrentNativeNodeRowLineage.lean:44.

The Mu compiler enters the actual extended domain, requests both bodies,
and then performs optionalBinder. maybeMu substitutes the repeated-pair
name, filters the callback's own bare root, and uses the normalized probe
key. A warm key can select an earlier payload. Request/probe identity and
causal History recover that actual winner; they do not select the current
losing candidate. NativeConstructReadback recovers current callbacks and
the stored winner. Its row identity conclusion is conditional on actual
usesLocal=false. RetainedMuWriterAlignment.reconstruct additionally uses
BinderFree of the recovered writer expression. StoredReconstruction.mu
constructs both sequential substitutions but claims no general equality.
Consequently these facts do not yet provide an unrestricted used nested-Mu
original-occurrence or exact continuation-anchor law. See Compile.lean:27,
MaybeMu.lean:20, NativeConstructReadback.lean:28, and
RetainedMuWriterAlignment.lean:273.

## ActualParentRowOrigins

Reviewed all three public proof bodies. No material issue was found.
reject_children derives exactly [Empty] from initial Good, with no child
availability premise. build_children derives either the accepted complete
children list or [Empty] from the literal checked constructor and initial
Good, loaded EqReady, and Values. edge handles raw contradiction before
field or child demand. Its accepted branch inverts the actual local return,
derives intermediate Good, Values, and EqReady from existing effects, then
invokes ActualLocalReduceRowOrigins.reduce. Both rejection cases give only
vacuous row Link through Empty. A positive surviving row excludes them.

The theorem has initial weak physical, conditional live-input, causal
GuardHeap, original source-footprint, and actual successful worker premises.
It does not assume Root, future semantic Reads, a desired output relation,
or a future child completion. It is a completed-call provenance theorem;
it does not construct general Parent or outer completion. The next outer
bridge must also cover warm edge winners using their actual earlier call
and the stated physical key invariants. SourceCurrentOuterRowFieldOrigins
already supplies full-field provenance at that separate boundary.

The current Haskell schedule has the same relevant serial shape:
reducePartially' maps reduceChildren after reduceEdgeIntersection;
reduceWithInheritedEcs applies indexed descent with zipWith. Recursive Mu
and union branches stop outer descent. This observation is limited to the
reviewed call order and does not assert full runtime correspondence. See
cfta/src/Data/CFTA/Equality/Operations.hs:80 and :93 and :143.

The final review manifest pins the exact source bytes and the selected
Parent strict/canonical/public receipts. Earlier warning-bearing attempts
remain preserved. The review reused existing production receipts. It added only the focused
source-construction checks described below; no Haskell check was run.

Final Parent source SHA is
ab6d401e21b276c18d0b2d61e087f6c2b16f5799651304ed7c014ef1835e11e0.
Selected root receipts are parent-origin-direct-3 (zero-byte log),
parent-origin-canonical-3 (1845 jobs; only the unchanged ClosedCompletion
warning), and parent-origin-public-2 (three full proof/signature/axiom
pairs, all eight options and only standard axioms). The three root public declarations are reviewed but not selected twice.
The selected schedule-footprint-kernels-public-1 group adds one full
constructed signature/proof/axiom pair. Its printer-free kernels2 log has
zero bytes. Its source build derives physical Facts and Available root.
The outer child at index 1 is the nested ordinary node. Productive smart
Mu values occur as closed captures and children. The two raw own fields
parse exactly as empty classes and one coherent [[0],[1]] class. The proof
uses endpoint [1] to refute the nested Unselected(1,1) condition. The failed
first attempt is preserved. All three fixture attempts execute immutable
snapshots with effective 4 GiB maximum/high, swap zero, and a five-minute
timeout. No additional production canonical run was needed.

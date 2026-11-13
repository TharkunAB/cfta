# Sublist Type-prefix observer plan

Status: planning only. No body or compiler run is included.
The proposed name is actual_identity_type_read_prefix_sublist.
The existing checked 327-line source and all its proof bodies stay unchanged.
Append the new private lemma within the same namespace if Root approves it.
The new header retains every old operational input and every old output receipt.
It adds only typePaths : List (List Int) and its pure Sublist relation.
Every fixed Needed.build [[0],[1],[2]] is replaced by Needed.build typePaths.
No nonempty, Matches, model, support, or readiness premise is added.

Proof stages

1. Retain the original actual source child lookup, singleton child proof, source
   closedness, and finite guarded identity witness from the same component call.
2. Set wanted := SourceEqualityNeeded.build typePaths.
   Use the existing generic actual_ordinary_singleton_type_child from the checked
   140-line basis. It already accepts arbitrary wanted and the same actual read.
   Retain the same prefix/Type/edge/suffix intervals and both Memos endpoints.
3. Keep the original prefix execution and semantic preservation proofs.
   Source-derived annotation.free=[] proves NodeSupport for all needed trees.
   No caller support or desired semantic membership is supplied.
4. Use build_valid typePaths. For build_nonnegative, transport each member
   path through typePathsSublist.subset to [[0],[1],[2]]. The old three-case
   proof then gives each signed key's nonnegativity. The universe remains
   arbitrary, and no raw goal or query admission condition is added.
5. Use the same node_exact, node_verified, and SemanticEffects.node observer
   at the SAME actual Type read. Keep its full Keeps/Ready/available/free and
   exact language-intersection conclusion.
6. Prove Matches wanted of the original finite arrow witness with build_exact.
   For each path member use typePathsSublist.subset, then the old three
   literal lookups. Matches is a derived conclusion, never a new premise.
7. Apply the exact language equivalence to that same original native witness.
   Retain all old final fields. No second Required/native producer is needed.

Empty paths and actual attachment

The generalized conditional header itself permits typePaths=[]. If its literal
function read is supplied, the inner Type request has empty Needed and the
existing identity constructors support it. This is mathematically consistent.
It does not mean that source compilation executes that function read.
The literal outer request in this header is node[(0,build typePaths)]. For []
that is node[(0,node[])], which differs from the empty request node[].

When the actual selected function-Type footprint is empty, the compiled full
request has no function-child entry. The actual RequireChildren.unselected and
ChildrenReads.unselected branches copy that function value. They create no
function NodeReads/row/Type subtrace. Composition must take this separate
identity branch. It must keep the actual earlier and later caches/Memos;
it must not declare the entire multi-child operation cache unchanged.
If an actual request explicitly visits an empty Needed at a node, use
RequireNode.identity/NodeReads.identity. That also does not manufacture the
nonempty outer function read required by the generalized observer.
The source annotation and finite witness remain attached to the SAME unchanged
value in the unselected branch. No visited Type result should be invented.

Alpha's actual precheck/scan observer must derive the pure Sublist and the
corresponding actual request shape. For a nonempty footprint its derived
function read can feed this observer. For an empty footprint it must feed the
unselected/identity branch instead. This is an operational composition seam,
not a public Matches/model/readiness provider and not a restriction of the goal.

No global emitted-Type history, joint model existence, partial input-assignment
pullback, gate result, default correspondence, or Haskell fix is claimed.

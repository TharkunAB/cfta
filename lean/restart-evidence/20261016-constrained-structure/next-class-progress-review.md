# Next class structural proof

Reviewed: 2026-10-16T16:28:37+02:00. This is a source inventory and proof proposal. It adds no
theorem and makes no new completion claim.

## Immediate boundary

The new native result theorem supplies finite ordinary output and a separate
height bound for each operand on the same actual checked trace
(`SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace`, lines 245–256).
`SourceCurrentAllocatedFiniteOrdinaryFinite.finite` constructs such a request
from initial Good, SemanticReady, native Stored, Idle, available domain
operands, and reached WordRanges. Its `original` and `closed` lemmas derive
original syntax and closed cached metadata from domain plus coherent residency.
The reviewed domain admits nonempty equality classes and all full guard fields.
It excludes Mu, references, and explicit unions throughout.

The next useful class theorem is positional:

```lean
NodeNarrow input result := DNode result ∧ height result ≤ height input
ForestNarrow inputs results := Language.All₂ NodeNarrow inputs results
```

These are proposed new predicates. Current path `Transport` is not this
predicate: it preserves NodeClosed paths only (`SourceCurrentEditDomains:43`).
Language narrowing also does not imply a physical shape or height bound,
including when the original language is empty.

## First missing component: actual memo merge domain

An edit leaf forces its class target and then intersects target with input
(`SourceCurrentAllocatedSharedTargetLeaf.Leaf.apply`, lines 34–39). Thus native
min-height can bound the result by input independently of target depth, once
both actual operands have the finite ordinary domain.

The target domain is not yet established. A target operand executes literal
`SourceEqualityProjectionGraph.Forest`, advances the same checked state, and
executes `SourceCurrentAllocatedMerge.Merge literalClear` at that state
(`SourceCurrentAllocatedTargetGraph.Operand.force`, lines 35–42).
Current merge Stored requires key identity, original/result availability and
conditional result closedness only (`SourceCurrentMemoMergeEffects:20–24`).
CacheCovers supplies language inclusion, not structural domain.

Recommended first additive theorem: derive finite ordinary result domain and
retention of a conditional structural merge-cache invariant through actual
`SourceCurrentAllocatedMergeGraph.Call`. A suitable new invariant is:

```lean
∀ key entry, memo key = some entry →
  DNode entry.original → DNode entry.result
```

Use the existing physical Stored in parallel. `hit_original` (Effects lines
49–58) recovers the complete captured original at a hit using common-heap
coherence. On a miss, prove the actual memo-aware body by Run/Call induction,
including its keep-first winner reread (AllocatedMergeGraph lines 149–154).
Do not replace this with an uncached body execution or an arbitrary recursive
callback law. The existing `EqualityMergedTargetHeight.Tree` has the same
finite ordinary shapes and useful constructor calculations; its
`worker_height`/`merge_height` endpoints concern the older cold worker, so they
are proof material, not a completed current-cache adapter.

For current body constructors (AllocatedMergeGraph lines 41–78): selection
retains original members (`SourceMergedSelection.retain_members`); retained
ordinary columns cannot take the recursiveBoundary/makeUnion branch; small
rows retain their raw guards; large groups allocate Top after actual columns;
makeNode creates an ordinary node or Empty. Domain alone is enough for target
admission. A same-input height bound for actual merge is useful but is not
needed to bound the edit result by its own input.

## Projection, slots, and actual edits

Add structural projection lemmas for the actual Forest/Project/ProjectRows,
Union, ReadAll and ordinary Read graphs. Missing paths give Empty; ordinary
paths select original child records; Union builds makeNode after ordered row
reads. Domain excludes the graph's recursive head branch. Use actual coherent
constructor readback and existing effects for intermediate residency. A
projection implementation is not supplied as a callback premise.

Compose projection domain with actual merge-domain retention to obtain
`Operand` and `Target` domain. Target Fold.cons runs its head operand, its tail
at the returned state, then the actual native Step at that tail's state
(TargetGraph lines 110–126). The new native theorem supplies the final domain.
Native structural Stored must also be retained through each actual query and
unchanged table advance.

Warm target slots need a separate causal sidecar such as
`∀ path value, state.targets path = some value → DNode value`.
Existing SharedTargetState.Ready and SlotReceipt provide availability,
closedness, language and historical graph receipts, but no finite ordinary
result condition (State lines 44–66). Empty class slots derive the sidecar;
a miss derives it from the actual target; a hit reads it. `Class.edit` starts
fresh slots around the same checked state and warm merge memo
(`SourceCurrentAllocatedClassEdits:31–37`), so a public compiled-class theorem
need not assume arbitrary prepopulated slot domains.

Then mutual induction over actual EditNode/EditChildren/EditRows yields
NodeNarrow, positional ForestNarrow, and per-row child bounds. Leaf uses the
actual native request certificate. Unselected children retain identity.
Ordinary rows use exact makeEdge children; makeNode filtering/canonical order
preserves the maximum bound. The recursive-head constructor is impossible
for a domain input. Reuse SharedEditEffects.node_physical/edge_physical and the
actual Reads for intermediate Ready/residency. No parent result law is needed.
Unequal path lengths and unequal selected subtree heights need no equal-depth
premise: the leaf bound is independently relative to the input being replaced.
Source path/trie precedence and index validity remain the actual graph's facts.

Compose Class.edit, ClassPass.Fold.cons tail-first, and Pass.done's literal
propagate. Each head class captures the forest returned by its tail. Erasure
and propagation replace positions with Empty and preserve positional bounds.
Existing ClassWorkerActual.verified/caller and SharedEditWorkerActual.*_verified
align supplied literal successes with these exact graphs; their current
receipts alone do not yet assert the new structural property.

## Local parent and recursive caller

Before class edits, current ScanClassPassActual.Reads.completed records the
actual scan, requireAll, and pass at their actual consecutive states. A small
independent RequireNode/Children/Rows structural proof is also necessary:
identity and missing-position rejection retain or delete rows; selected
children recurse; raw constructors preserve domain and height. The current
RequiredGraph contains no structural-height endpoint. This proof has no native
leaf and is a bounded independent component.

Combine that with class ForestNarrow in LocalReductionActual.verified/finite.
Precheck trivial returns the original forest. Contradiction and a stopped scan
erase positions. A live completed scan performs requireAll and class Pass.
Existing local receipts retain length and language but not the new bound.
At the actual final MkEdge, Receipt.children chooses the returned local forest
or singleton Empty (`SourceCurrentAllocatedMkEdge:62–70`). Raw rejection runs
before local work and needs no child/range premise. Derive a generalized parent
certificate `DEdge result ∧ edgeHeight result ≤ edgeHeight request.value` at
the exact ParentWorkerActual.resident_finite/resident_verified return.

The older ReturnedDomain.Shape is too strong for class narrowing: it permits
only original children, erased positions, or singleton Empty (lines 25–28).
Replace it additively with a conditional edge structural certificate tied to
the actual stored owner, and prove its warm lookup/demand/finish lifecycle.
A newly intersected child can differ physically from all three old shapes.
Actual owner/key equality must precede reading that certificate. Existing
NoNewActive and selected-owner frame retention are still reusable. Returned
child height is then strictly below its original ordinary parent, so a new
height induction can use generated children without a finite-future-key oracle.
Do not substitute this condition for Region in frozen plain theorems; make a
new finite ordinary recursive theorem with the same actual state threading.

## Remaining explicit premises

The first completion composition can reuse existing current Context, allocated
field lookup/history, inherited Ready, selected path support, global and fourth
memo correctness, and reached range plans. Initial native/merge structural
cache invariants must be derived from empty tables or actual earlier
productions; existing semantic Context does not imply them automatically.

`LocalReductionActual.Ranges` inspects the actual precheck classes branch;
ClassPass/Target/Leaf ranges inspect actual reached prefix states. They contain
machine WordRanges, not future success or semantic result laws. Structural
preservation will not by itself prove that every dynamic machine key fits its
width. Do not replace these checks by a finite list of assumed future keys.
Finite ordinary domain closure should separately derive the required closed
path support from coherent resident descendants, rather than request a future
projected result or a semantic answer.

General Mu/union inputs, arbitrary malformed/warm caches, concrete GHC forcing,
concurrent publication, host key-map correspondence, and whole-library
completion remain outside this next stage. This review found no new Haskell
defect and ran no compiler, Lake, or source validation command.

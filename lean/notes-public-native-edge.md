# Exact public language of the complete guarded native edge pass

Updated: 2026-10-15 07:42 CEST.
Proofs: `5680b122`, `062ec3e5`, and `5c15f84c`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

Actual inherited/local physical payload combination and trie descent are now
proved. Indexed children derive their own obligations and preserve actual
scopes and language under an explicit recursive-node induction hypothesis.
The concrete native edge step composes with this inherited continuation.
The outer node/row worker and actual Mu reconstruction still need to derive
that hypothesis. Read [the current note](notes-inherited-edge.md).

## Actual general merge effects

SourceMergedAnnotationComparison.Effect retains source cache histories,
complete semantic readiness, and a physical annotation preservation function.
Its callback law applies only at actual closed available inputs and successful
returned states. children_effect, anyCover_effect, allRows_effect, and check_effect
follow the literal repaired comparison worker. Actual comparison reads can
allocate Mu records. Their annotations follow the proved source exposure path.

SourceMergedAnnotationSelection proves any_effect, retain_effect, and select_effect.
It follows ordered recursive covers, retained closed Mu operands, and the final
canonical identity filter. Source definitions and returned heaps are unchanged.

SourceMergedAnnotationWorker.map_heap advances input scopes through actual prior
effects. RecurseHeap concerns only actual successful recursive calls. The final
worker_heap theorem derives it by ordinary-fuel induction; callers supply no
whole-worker annotation law. Existing source correctness supplies intermediate
closed availability and cache history. It is specialized to the always-true
guard meaning only where the annotation proof needs those cache effects.

retained_heap covers the singleton, recursive createUnion, and ordinary union
branches. column_heap first retains the actual repaired filter effects.
small_heap obtains the emitted full guard check from the original resident edge
record. large_heap checks the literal Top guard. group_heap retains the source
four-row threshold. root_heap makes a node after every actual ordered group.
execute_heap uses executable source grouping and the original derived height.
It derives the result heap, without an assumed future annotation invariant.

## Captured target demands and shared edits

SourceEqualityAnnotationTarget.merge lifts actual general merging to the retained
full native state. operand composes actual captured-forest projection with this
merge. fold follows the first-seeded right fold: demand the left operand, finish
the tail, then run native intersection in that returned warm state. target covers
the empty and nonempty lists.

force covers both shared closure branches. A hit changes no heap or slot. A miss
uses the actual captured original forest and stores its returned physical target.
leaf then runs the actual native request at the first-force returned state.
Native empty and conjoined guards use the preceding annotation constructor proofs.

SourceEqualityAnnotationSharedEdit proves node, children, rows, and list by mutual
graph induction. Callback tokens refer to original class paths. Existing shared
state effects derive original capture scope, target receipts, warm native
validity, and every intermediate available input. Actual head reads retain
annotations. Every rebuilt row obtains its full guard check from its original
resident edge record. No eager target or future annotation heap is assumed.

## Selected class and one-pass composition

SourceEqualityAnnotationPass.class_heap starts fresh unforced closures at the
actual class entry forest. fold_heap runs the tail before the next fresh class.
pass_heap retains the single final empty propagation and its unchanged native
heap. This is the actual source fold schedule.

selected_required_heap uses SourceClosedGateCache.selection_state to derive the
unchanged constructor heap of closed source gate selection. It then uses the
actual required-path graph and annotation theorem. It does not assume general
unfolding has no allocation. selected_heap composes these actual receipts with
the selected native pass.

one_pass_heap covers unchanged, erased, live, and checked error branches.
guarded_edge_heap follows actual source payload readback and the actual pass,
then literal makeEdge with the original symbol and complete original constraint.
It derives the final physical edge-record annotation heap.

## Exact public readback

SourceEqualityPublicNativeEdge fixes complete source labels and constraints,
actual SourceMemoGate controls, actual noConstraint Top, and structural-order
source conjunction. Actual Top and conjoin theorems derive all emitted cached
payload checks. No unrestricted public guard-conjunction law is supplied.

language derives the final annotation heap. Actual resident records derive
annotations for the original edge and returned edge. edge_public_eq transports
both complete PCS edge meanings to the current public acceptsConstraint meaning.
The independent guarded-edge theorem then gives unconditional public narrowing
and exact public input/output edge meaning when inherited constraints hold.
The theorem applies to every actual completed guarded edge pass in an idle
closed available native scope with the initial annotation heap.

source_edges starts with original closed syntax whose literal stored annotations
have the normalized source representation. Original construction derives that
initial annotation heap. Actual finite source completion gives the guarded-edge
graph, both source gate memo certificates, final idle validity, both constructor
histories, result residency, closed children, original complete labels, stable
six-stage worker answers, and eventual bounded-array answers. Only actual
reached primitive native word checks remain explicit.

The theorem does not assume the output annotation invariant or a complete pass
language law. It does not extend public conjunction to malformed raw stored
singleton payloads. The previous singleton_storage_boundary remains unchanged.
The earlier PCS output/public input theorem remains valid as a preserved proof.

## Next actual caller boundary

The guarded native edge pass implements the local reduceEdgeIntersection step.
The outer reducePartially caller also combines inherited and local payloads,
descends them by child index, recursively processes the narrowed children,
sets those children on the original full edge, and modifies the original node.
Its Mu branch invokes the smart constructor. Explicit unions and empty nodes
return unchanged; a free Rec is an error.

PartialReductionCaller already proves completed high-level caller preservation
under local representation and operation laws. Read notes-partial-reduction-caller.md.
Next derive actual source combined-payload and eqConstraintsDescend readback,
then build the physical caller graph and bounded worker. Use the concrete local
edge theorem here. Retain exact cache effects, signed or natural index adapters,
original labels, checked errors, and incomplete observations. Do not replace
whole-child traversal with a supplied forest preservation law.

Prove completed caller preservation before any general termination claim.
The finite local edge theorem does not prove whole-caller termination. Native
intersection can increase ordinary depth, so the original cached depth is not
a general traversal measure. Retain the existing depth and cycle boundaries.
Open contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain separate. Sized exact classes, finite size
execution, size order, both rank inverses, and the optimized core are retained.

## Validation and preservation

All seven new modules pass focused Lean 4.34.1 builds. The aggregate audit passes
1,806 jobs and 47,797 theorem dependency checks. Only propext, Classical.choice,
and Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-public-native-edge-20261015-audit.log.
Snapshot: /tmp/mcfta-public-native-edge-checkpoint-20261015-0742/.
It retains 2,215 Lean-tree files and four root documents. Older proofs except
audit imports, all counterexamples, marked drafts, production source, stashes,
and other worktrees are unchanged. The earlier 645 Haskell examples and formatter
checks apply to the unchanged source and were not rerun.

The Lava paper's explicit function and graph method applies to this composition.
It does not discharge the actual inherited caller, runtime scheduling, or
extraction. No Lava or Rocq dependency is added.

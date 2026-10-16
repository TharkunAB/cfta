import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
import MicroCFTA.SourceCurrentAllocatedPartialWorkerActual

namespace MicroCFTA.ActiveFramesReview
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialActiveOrder
open SourceCurrentAllocatedPartialActiveFrames (NoNewActive)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

-- Supplied literal success derives its own completed graph and preserves arbitrary ancestor exclusions.
theorem literal_success_restores {width : Nat} {before after : Caller width}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {memos : Memos}
    {request : NodeRequest} {result : Node} {f g s r e p h m c n budget bound : Nat}
    {nodeSkip edgeSkip : Option Nat}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (active : ActiveExcept bound nodeSkip edgeSkip before)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall f g s r e p h m c n budget request before)
    (done : SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before = .done result after) :
    ∃ next saved, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos saved ∧
      Post formulas solver next before after saved ∧ NoNewActive before after ∧
      ActiveExcept bound nodeSkip edgeSkip after := by
  obtain ⟨next, saved, actual, reads, _checks, post, _available, _law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.nodeCall_verified formulas solver initial inherited available ranges done
  have frame := SourceCurrentAllocatedPartialActiveFrames.node_call actual
  exact ⟨next, saved, actual, reads, post, frame, frame.activeExcept active⟩

-- Exact owner publication, completed body, and finish restore the parent bound and return that owner.
theorem owner_finish_restores {width : Nat} {before running middle : Caller width}
    {request owner : NodeRequest} {result : Node} {handle budget bound : Nat}
    (protocol : SourceCurrentAllocatedPartialFrames.Protocol before)
    (active : ActiveAbove bound before)
    (started : beginNode request before = (handle, .evaluate owner, running))
    (body : NodeBody budget owner running result middle) :
    ActiveAbove bound (finishNode handle result middle) ∧
      (finishNode handle result middle).nodeResults.cells handle = some ⟨owner, .returned result⟩ ∧
      NoNewActive before (finishNode handle result middle) := by
  have except := beginNode_except request before active
  rw [started] at except
  have restored := (SourceCurrentAllocatedPartialActiveFrames.node_body body).activeExcept except
  have published := SourceCurrentAllocatedPartialFrames.beginNode_frame request before protocol
  rw [started] at published
  have exactOwner := (SourceCurrentAllocatedPartialFrames.beginNode_owner request before handle owner running protocol started).1
  have forward := SourceCurrentAllocatedPartialFrames.node_body body published.valid
  have retainedOwner := forward.node_running handle owner exactOwner
  exact ⟨finishNode_above result restored, finishNode_returned handle owner result middle retainedOwner,
    SourceCurrentAllocatedPartialActiveFrames.node_call (.evaluate started body)⟩

-- Rank push admits smaller recursive work. A completed body then restores the stronger parent bound.
theorem rank_push_and_restore {width : Nat} {before running middle : Caller width}
    {request owner : NodeRequest} {result : Node} {handle lower budget : Nat}
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (active : ActiveAbove (nodeRank request) before)
    (smaller : lower < nodeRank request)
    (started : beginNode request before = (handle, .evaluate owner, running))
    (body : NodeBody budget owner running result middle) :
    ActiveAbove lower running ∧ ActiveAbove lower middle ∧
      ActiveAbove (nodeRank request) (finishNode handle result middle) ∧
      (finishNode handle result middle).nodeResults.cells handle = some ⟨owner, .returned result⟩ := by
  have pushed := node_push formulas solver sound coherent inherited available active smaller started
  have bodyFrame := SourceCurrentAllocatedPartialActiveFrames.node_body body
  have finished := owner_finish_restores (SourceCurrentAllocatedPartialFrames.Protocol.of_valid sound.valid) active started body
  exact ⟨pushed, bodyFrame.activeExcept pushed, finished.1, finished.2.1⟩

-- Source row order completes parent narrowing and descendants of the RETURNED edge before the suffix.
theorem row_prefix_before_sibling {width : Nat} {before middle afterChildren : Caller width}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {memos : Memos}
    {inherited : SourceEqualityConstraintAllocation.Value} {original narrowed result : Edge}
    {f g s r e p h m c n budget bound : Nat} {nodeSkip edgeSkip : Option Nat}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap original)
    (active : ActiveExcept bound nodeSkip edgeSkip before)
    (edgeRanges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall f g s r e p h m c n budget ⟨inherited, original⟩ before)
    (edgeDone : SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
    (childRanges : SourceCurrentAllocatedPartialWorkerRanges.descendants f g s r e p h m c n budget inherited narrowed middle)
    (childDone : SourceCurrentAllocatedPartialWorker.descendants f g s r e p h m c n budget inherited narrowed middle = .done result afterChildren) :
    ∃ next saved,
      Post formulas solver next before afterChildren saved ∧
      NoNewActive before afterChildren ∧ ActiveExcept bound nodeSkip edgeSkip afterChildren ∧
      InternedEdgeResidency.EdgeResident afterChildren.checked.native.machine.heap result := by
  obtain ⟨edgeInventory, edgeMemos, edge, _edgeReads, _edgeChecks, edgePost, edgeResident, _edgeLaw⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.edgeCall_verified formulas solver initial inheritedReady resident edgeRanges edgeDone
  have middleInherited := inheritedReady.grows edgePost.effects.grows.constraint_growth
  obtain ⟨next, saved, children, _reads, _checks, childrenPost, output, _law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.descendants_verified formulas solver edgePost.context middleInherited
      edgeResident childRanges childDone
  have frame := (SourceCurrentAllocatedPartialActiveFrames.edge_call edge).trans
    (SourceCurrentAllocatedPartialActiveFrames.descendants children)
  exact ⟨next, saved, edgePost.trans childrenPost, frame, frame.activeExcept active, output⟩

end MicroCFTA.ActiveFramesReview
#print axioms MicroCFTA.ActiveFramesReview.literal_success_restores
#print axioms MicroCFTA.ActiveFramesReview.owner_finish_restores
#print axioms MicroCFTA.ActiveFramesReview.rank_push_and_restore
#print axioms MicroCFTA.ActiveFramesReview.row_prefix_before_sibling

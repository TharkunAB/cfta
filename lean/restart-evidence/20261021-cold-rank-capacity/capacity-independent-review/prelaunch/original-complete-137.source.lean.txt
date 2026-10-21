import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentOuterRankAdequacy
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentConstructedOuterInitial
import MicroCFTA.SourceCurrentParentInitialRoom

open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialWorker (nodeCall)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentOuterRankEnvelope (envelope)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

namespace MicroCFTA.SourceCurrentColdRankCapacity

theorem constructed_initial_node_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {initial finalCache : Cache.State SourceEqualityPartialConstraintKey.Key}
    {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initial finalCache originals)
    (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ originals)
    (budget : Nat) :
    ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
    let seed : List Guard × Profile := (SourceEqualityConstraintOrigins.guards expression,
      ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)
    let request : NodeRequest := ⟨SourceCurrentAllocatedPartialInitialization.emptyValue finalCache, value⟩
    let output := envelope budget
      (SourceCurrentPositiveQuotientCount.count (request.inherited.payload.getD []) value)
      (InternedValueMass.value value) seed
    let joined := SourceCurrentInitialSelectionForecast.cover [output.2.2.2]
      (SourceCurrentOuterInitialSchedule.node output.1 budget seed).2
    let bits := SourceCurrentParentInitialRoom.roomBits joined
    let before := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) finalCache heap
    let first : Phase (bits + 2) := .node output.1 request before
    let need := SourceCurrentOuterInitialFuel.phaseNeed budget first seed
    ∃ (result : Node) (after : Caller (bits + 2)), ∀ fuel, output.1 ≤ fuel →
      nodeCall fuel need need need need need need need need need budget request before = .done result after
 := by
  let alphabet := SourceEqualityConstraintOrigins.guards expression
  have allowed : SourceEqualityAnnotationConstruction.Allowed
      (fun guard => guard ∈ alphabet) expression :=
    SourceEqualityConstraintOrigins.allowed _ expression (fun _ member => member)
  obtain ⟨value, heap, built, physicalCarrier, _annotated⟩ :=
    SourceEqualityAnnotationConstruction.closed (fun guard => guard ∈ alphabet) expression allowed
  refine ⟨value, heap, built, ?_⟩
  let seed : List Guard × Profile := (alphabet,
    ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)
  let request : NodeRequest := ⟨SourceCurrentAllocatedPartialInitialization.emptyValue finalCache, value⟩
  let output := envelope budget
    (SourceCurrentPositiveQuotientCount.count (request.inherited.payload.getD []) value)
    (InternedValueMass.value value) seed
  let joined := SourceCurrentInitialSelectionForecast.cover [output.2.2.2]
    (SourceCurrentOuterInitialSchedule.node output.1 budget seed).2
  let bits := SourceCurrentParentInitialRoom.roomBits joined
  let before := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) finalCache heap
  let first : Phase (bits + 2) := .node output.1 request before
  let need := SourceCurrentOuterInitialFuel.phaseNeed budget first seed
  let inventory := SourceCurrentAllocatedPartialInitialization.inventory expression value heap built
  change ∃ (result : Node) (after : Caller (bits + 2)), ∀ fuel, output.1 ≤ fuel →
    nodeCall fuel need need need need need need need need need budget request before = .done result after
  obtain ⟨context, identity, same, inheritedReady, available, closed, _original⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed (bits + 2) history valid
      expression covered value heap built formulas solver
  have initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before
      SourceCurrentAllocatedPartialInitialization.globals := context
  have inherited : SourceEqualityConstraintAllocation.Ready
      before.checked.operations.constraints request.inherited := by
    change SourceEqualityConstraintAllocation.Ready
      before.checked.operations.constraints (SourceCurrentAllocatedPartialInitialization.emptyValue finalCache)
    rw [same]
    exact inheritedReady
  have frame : SourceCurrentConstrainedCapGeneratedQueryResources.Frame
      formulas solver inventory before.checked :=
    SourceCurrentConstructedOuterInitial.frame formulas solver inventory
      ⟨heap, Cache.emptyState⟩ (SourceCurrentAllocatedPartialInitialization.operations finalCache)
      expression value built initial.ready
      (SourceCurrentAllocatedPartialInitialization.inventory_source expression value heap built)
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  have numeric : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 before.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      before.checked.native.machine.heap := physicalCarrier
  have inputs : SourceCurrentOuterPrefixInvariants.Inputs first := ⟨inherited, available⟩
  have room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      (SourceCurrentInitialSelectionForecast.cover [output.2.2.2]
        (SourceCurrentOuterInitialPrefix.forecast budget first seed).2) :=
    SourceCurrentParentInitialRoom.room_computed joined
  have normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentRequiredUnionNormal.source expression
  have supported : SourceCurrentNativeRequestPositivePositions.Support
      before.checked.native.machine.heap before.checked.native :=
    ⟨FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩
  have causal : SourceCurrentNativeMuPublication.History empty before.checked.native.machine.heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentNativeMuPublication.closed_history expression
  have merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) before.merge :=
    SourceCurrentConstrainedCapMemoMerge.stored_empty _
  have positiveMemo : SourceCurrentMergePositivePosition.Support before.merge :=
    SourceCurrentMergePositivePosition.support_empty
  have origins : SourceCurrentResourceParentWriters.Origins formulas solver before :=
    SourceCurrentResourceParentWriters.initial formulas solver
      (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) finalCache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  have stored : SourceCurrentOuterClosedInputs.NodeStored before :=
    SourceCurrentOuterClosedInputs.initial
      (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) finalCache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  have inputClosed : SourceCurrentOuterClosedInputs.InputsClosed first := closed
  have nodeIdle : ∀ chosen owner, before.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩ := by
    intro chosen owner impossible
    cases impossible
  have edgeIdle : SourceCurrentOuterEdgeIdle.EdgeIdle before :=
    SourceCurrentOuterEdgeIdle.initial
      (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) finalCache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  exact SourceCurrentOuterRankAdequacy.initial_node_call
    (bits := bits) (g := need) (s := need) (r := need) (e := need) (p := need)
    (h := need) (m := need) (c := need) (n := need)
    formulas solver seed initial frame numeric carrier inputs room normal supported causal merged positiveMemo
      origins stored inputClosed nodeIdle edgeIdle
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

end MicroCFTA.SourceCurrentColdRankCapacity

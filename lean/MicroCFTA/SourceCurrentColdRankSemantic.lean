import MicroCFTA.SourceCurrentColdRankCapacity
import MicroCFTA.SourceCurrentConstructedOuterInitial

namespace MicroCFTA.SourceCurrentColdRankSemantic
open Cache InternedConstructorTemplates InternedProbeProvenance
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
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
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
    ∃ (result : Node) (after : Caller (bits + 2)),
      (∀ fuel, output.1 ≤ fuel →
        nodeCall fuel need need need need need need need need need budget request before = .done result after) ∧
      Available after.checked.native.machine.heap result ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term
 := by
  obtain ⟨value, heap, built, result, after, stable⟩ :=
    SourceCurrentColdRankCapacity.constructed_initial_node_call
      formulas solver history valid expression covered budget
  refine ⟨value, heap, built, ?_⟩
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
  let inventory := SourceCurrentAllocatedPartialInitialization.inventory expression value heap built
  change ∃ (result : Node) (after : Caller (bits + 2)),
    (∀ fuel, output.1 ≤ fuel →
      nodeCall fuel need need need need need need need need need budget request before = .done result after) ∧
    Available after.checked.native.machine.heap result ∧
    ∀ ambient term,
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term
  have stableSame : ∀ fuel, output.1 ≤ fuel →
      nodeCall fuel need need need need need need need need need budget request before = .done result after := stable
  have called := stableSame output.1 (Nat.le_refl _)
  obtain ⟨context, identity, same, inheritedReady, available, _closed, _original⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed (bits + 2) history valid
      expression covered value heap built formulas solver
  have initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before
      SourceCurrentAllocatedPartialInitialization.globals := context
  have inherited : SourceEqualityConstraintAllocation.Ready
      before.checked.operations.constraints request.inherited := by
    change SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints
      (SourceCurrentAllocatedPartialInitialization.emptyValue finalCache)
    rw [same]
    exact inheritedReady
  have inputAvailable : InternedProbeProvenance.Available
      before.checked.native.machine.heap request.value := available
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  have fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 before.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have allowed : SourceEqualityAnnotationConstruction.Allowed
      (fun guard => guard ∈ seed.1) expression :=
    SourceEqualityConstraintOrigins.allowed _ expression (fun _ member => member)
  have carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      before.checked.native.machine.heap := by
    change SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) heap
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceEqualityAnnotationConstruction.build (fun guard => guard ∈ seed.1) expression allowed
        [] empty (SourceEqualityAnnotationHeap.empty_heap _)
  have roomJoined : SourceCurrentAllocatedNativeResourceForecast.Room bits joined :=
    SourceCurrentParentInitialRoom.room_computed joined
  have room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      (SourceCurrentOuterInitialSchedule.node output.1 budget seed).2 :=
    roomJoined.mono (SourceCurrentInitialSelectionForecast.cover_ge _ _)
  obtain ⟨resultAvailable, law⟩ := SourceCurrentConstructedOuterInitial.node_call
    formulas solver expression value ⟨heap, Cache.emptyState⟩
    (SourceCurrentAllocatedPartialInitialization.operations finalCache)
    built before after inventory SourceCurrentAllocatedPartialInitialization.globals rfl
    (SourceCurrentAllocatedPartialInitialization.inventory_source expression value heap built)
    initial seed fits carrier request inherited inputAvailable
    output.1 need need need need need need need need need budget room result called
  refine ⟨result, after, stableSame, resultAvailable, ?_⟩
  intro ambient term
  apply ((law ambient term).2 ?_).symm
  simp [request, same, SourceEqualityConstraintAllocation.Value.payload,
    SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

end MicroCFTA.SourceCurrentColdRankSemantic

import MicroCFTA.SourceCurrentOuterInitialWorkerRanges
import MicroCFTA.SourceSynthesisOriginalRankCompletion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

/-!
# Actual worker range checks from the original cold caller

Accepted source input derives allocation preparation, the physical build,
the initial caller, and its resource frame. Actual initial record reads
compute the finite guard list and the payload mass bound.

Room for the finite-fuel forecast remains an explicit numeric premise.
The range result covers the actual bounded run, including a failed run.
It does not assume successful execution or a future range plan. It does
not derive unbounded completion, native word capacity, or a driver bound.
-/
namespace MicroCFTA.SourceSynthesisOriginalWorkerRanges
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue operations inventory globals)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceSynthesisOriginalRankCompletion (seed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Original input and numeric forecast room derive all actual bounded worker ranges. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression) (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      Context formulas solver (inventory (ordinarySymbols expression) value heap built)
        (caller (bits + 2) cache heap) globals ∧
      Frame formulas solver (inventory (ordinarySymbols expression) value heap built)
        (caller (bits + 2) cache heap).checked ∧
      Fits (seed heap).2 (caller (bits + 2) cache heap).checked ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap ∧
      Available heap value ∧ value.free = [] ∧
      ∀ fuel g s r e p h m c n budget,
        Room bits (SourceCurrentOuterInitialPrefix.forecast budget
          (.node fuel (⟨emptyValue cache, value⟩ : NodeRequest) (caller (bits + 2) cache heap))
          (seed heap)).2 →
        SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget
          (⟨emptyValue cache, value⟩ : NodeRequest) (caller (bits + 2) cache heap) := by
  obtain ⟨fields, cache, value, heap, built, prepared, context, facts, available, _roles,
      _growth, _history, _identity, emptySame, inherited, closed, _original⟩ :=
    SourceSynthesisOriginalCallerInitialization.accepted lib query signed expression returned (bits + 2)
      Cache.emptyState Cache.empty_valid formulas solver
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap
      SourceCurrentConstrainedCapCheckedJointClosed.Plain heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentConstrainedCapGuardExecution.closed_heap
        SourceCurrentConstrainedCapCheckedJointClosed.Plain (ordinarySymbols expression)
  have frame : Frame formulas solver (inventory (ordinarySymbols expression) value heap built)
      (caller (bits + 2) cache heap).checked :=
    Frame.initial formulas solver (inventory (ordinarySymbols expression) value heap built)
      ⟨heap, Cache.emptyState⟩ (operations cache) context.ready guards rfl
  have fits : Fits (seed heap).2 (caller (bits + 2) cache heap).checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap :=
    SourceCurrentConjunctionGuardUniverse.initial heap facts
  have ready : SourceEqualityConstraintAllocation.Ready
      (caller (bits + 2) cache heap).checked.operations.constraints (emptyValue cache) := by
    rw [emptySame]
    exact inherited
  refine ⟨fields, cache, value, heap, built, prepared, context, frame, fits, known, available, closed, ?_⟩
  intro fuel g s r e p h m c n budget room
  exact SourceCurrentOuterInitialWorkerRanges.nodeCall_ranges formulas solver (seed heap)
    context frame fits known ready available room

end MicroCFTA.SourceSynthesisOriginalWorkerRanges

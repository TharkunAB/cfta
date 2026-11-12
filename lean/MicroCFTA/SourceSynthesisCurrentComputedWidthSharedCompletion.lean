import MicroCFTA.SourceSynthesisCurrentCheckedHereditarySharedCompletion
import MicroCFTA.SourceSynthesisCurrentInitialComputedRoom

/-!
# Current checked completion at a computed mathematical width

The original source input and budget select a sufficient mathematical width.
One checked producer retains its complete initializer and worker endpoint.
The same returned build discharges its exact initial Room condition.
This does not prove capacity at a fixed Haskell machine width.
-/
namespace MicroCFTA.SourceSynthesisCurrentComputedWidthSharedCompletion
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceSynthesisNativeTypeTrace (Origin cold)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedSharedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue checked operations inventory globals)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "TypeReady" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "History" => SourceSynthesisHereditaryClosedMemo.History
local notation "NodeFields" => SourceSynthesisHereditaryClosedMemo.NodeFields
local notation "envelope" => SourceCurrentSharedOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Current source success retains the complete checked return at its computed mathematical width. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (budget : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let bits := SourceSynthesisCurrentInitialComputedRoom.bits lib query signed budget
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (inventory (ordinarySymbols expression) value heap built)
        (caller (bits + 2) cache heap) globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (caller (bits + 2) cache heap).checked.operations.constraints (.live identity []) ∧
        value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
        let request : NodeRequest := ⟨emptyValue cache, value⟩
        let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
        let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
        let need := phaseNeed budget first (seed heap)
        ∃ result after,
          SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
            output.1 need need need need need need need need need budget request
            (caller (bits + 2) cache heap) ∧
          (∀ fuel, output.1 ≤ fuel →
            nodeCall fuel need need need need need need need need need budget request
              (caller (bits + 2) cache heap) = .done result after) ∧
          (∀ fuel, output.1 ≤ fuel →
            SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
              fuel need need need need need need need need need budget request
              (caller (bits + 2) cache heap)) ∧
          ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.NodeCall budget request
              (caller (bits + 2) cache heap) result after,
            SourceCurrentAllocatedSharedPartialChecks.Checks
              (SourceCurrentAllocatedSharedPartialChecks.nodeCallTrace graph) ∧
            SourceCurrentAllocatedSharedPartialEndpointReads.NodeCallReads formulas solver graph globals final ∧
            Post formulas solver next (caller (bits + 2) cache heap) after final ∧
            Frame formulas solver next after.checked ∧
            Fits (forecast budget first (seed heap)).2 after.checked ∧
            SourceEqualityAnnotationHeap.Heap
              (fun guard => guard ∈ (forecast budget first (seed heap)).1) after.checked.native.machine.heap ∧
            Available after.checked.native.machine.heap result ∧
            SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧
            SharedReady (encodedLibrary lib) (initialShared after.checked after.merge) ∧
            GuardHeap (Origin (encodedLibrary lib)) after.checked.native.machine.heap ∧
            History (encodedLibrary lib) literal after ∧ result.free = [] ∧
            NodeFields (encodedLibrary lib) literal request result ∧
            ValueFields (Origin (encodedLibrary lib)) literal result := by
  dsimp only
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame,
      inherited, closed, original, complete⟩ :=
    SourceSynthesisCurrentCheckedHereditarySharedCompletion.accepted lib query signed expression returned
      (SourceSynthesisCurrentInitialComputedRoom.bits lib query signed budget) budget formulas solver
  have room := SourceSynthesisCurrentInitialComputedRoom.room_of_build lib query signed expression returned
    budget value heap built cache
  exact ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame,
    inherited, closed, original, complete room⟩

end MicroCFTA.SourceSynthesisCurrentComputedWidthSharedCompletion

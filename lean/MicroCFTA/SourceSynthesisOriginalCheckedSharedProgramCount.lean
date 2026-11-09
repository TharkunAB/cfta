import MicroCFTA.SourceSynthesisOriginalCheckedHereditarySharedCompletion
import MicroCFTA.SourceSynthesisOriginalProgramTermSize

/-!
# Source component counts at the same checked shared return

One original checked completion supplies the build and all returned state.
Its immutable NodeLaw maps each accepted result term to that original root.
The source-size theorem uses the same build to derive the Program projection
and component count. No second initialization or capacity test is used.

The endpoint retains the full graph, ordered reads, Post, resource facts,
Type facts, history and hereditary fields. The component count does not
supply enumeration depth, selected class order, ranks, native word bounds,
or global Haskell interning correspondence.
-/
namespace MicroCFTA.SourceSynthesisOriginalCheckedSharedProgramCount
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedSharedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue globals)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "History" => SourceSynthesisHereditaryClosedMemo.History
local notation "NodeFields" => SourceSynthesisHereditaryClosedMemo.NodeFields
local notation "envelope" => SourceCurrentSharedOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
local notation "cover" => SourceCurrentInitialSelectionForecast.cover
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The same complete checked return retains the original requested Program component count. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression) (bits budget : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ _built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      let request : NodeRequest := ⟨emptyValue cache, value⟩
      let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
      let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
      let need := phaseNeed budget first (seed heap)
      Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) →
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
          SharedReady lib (initialShared after.checked after.merge) ∧
          GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after ∧
          result.free = [] ∧ NodeFields lib literal request result ∧ ValueFields (Origin lib) literal result ∧
          ∀ ambient term,
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
            ∃ program, SourceSynthesisProgramTermSize.Projection literal Prod.fst term program ∧
              SourceSynthesisProgramTermSize.toProgram literal Prod.fst term = program ∧
              program.components = signed.toNat := by
  obtain ⟨fields, cache, value, heap, built, prepared, complete⟩ :=
    SourceSynthesisOriginalCheckedHereditarySharedCompletion.accepted
      lib query signed expression returned bits budget formulas solver
  let request : NodeRequest := ⟨emptyValue cache, value⟩
  let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
  let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
  refine ⟨fields, cache, value, heap, built, prepared, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, baseRanges, done, allRanges, next, final, graph,
      checks, reads, post, afterFrame, afterFits, afterKnown, available, law,
      typed, guards, history, closed, nodeFields, valueFields⟩ := complete room
  refine ⟨result, after, baseRanges, done, allRanges, next, final, graph,
    checks, reads, post, afterFrame, afterFits, afterKnown, available, law,
    typed, guards, history, closed, nodeFields, valueFields, ?_⟩
  intro ambient term accepted
  have mappedBuilt : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  exact SourceSynthesisOriginalProgramTermSize.firstOrderRaw_build_accepted literal Prod.fst
    lib query signed expression returned value heap mappedBuilt
    (SourceEqualityPCSGuard.holds formulas solver) ambient term ((law ambient term).1 accepted)

end MicroCFTA.SourceSynthesisOriginalCheckedSharedProgramCount

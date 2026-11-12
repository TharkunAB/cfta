import MicroCFTA.SourceSynthesisCurrentComputedWidthSharedCompletion
import MicroCFTA.SourceSynthesisCurrentRootTyping
import MicroCFTA.InternedGuardedExecution

/-!
# Ordinary typing at the actual checked shared return

One computed-width producer retains its complete initializer and worker endpoint.
Every term accepted by its returned result retains ordinary typing at the query goal.
The proof uses the same returned NodeLaw and the same original build.
It does not execute enumeration or assert fixed machine capacity.
-/
namespace MicroCFTA.SourceSynthesisCurrentComputedWidthTypedSharedCompletion
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
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisPr210TypeReflection (candidateRigid)
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
private theorem meaning_decider_eq
    (first second : DecidableEq FullSyntax.Formula)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (value : Node) (term : Language.Term Symbol) :
    InternedGuardedLanguage.meaning
      (@SourceEqualityPCSGuard.holds FullSyntax.Formula first formulas solver) ambient value term =
    InternedGuardedLanguage.meaning
      (@SourceEqualityPCSGuard.holds FullSyntax.Formula second formulas solver) ambient value term :=
  congrArg (fun decider : DecidableEq FullSyntax.Formula =>
    InternedGuardedLanguage.meaning
      (@SourceEqualityPCSGuard.holds FullSyntax.Formula decider formulas solver) ambient value term)
    (Subsingleton.elim first second)

variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The full checked return types every term accepted by that same returned native value. -/
theorem accepted_typed
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
            ValueFields (Origin (encodedLibrary lib)) literal result ∧
            ∀ ambient term,
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
              ∃ program body,
                term = .node (literal "filter") [candidateRigid query.queryGoal, body] ∧
                Typed lib query program query.queryGoal ∧
                term.atPath [0] = some (candidateRigid query.queryGoal) ∧
                body.atPath [0] = some (candidateRigid query.queryGoal) ∧
                Projection literal Prod.fst term program ∧
                toProgram literal Prod.fst term = program ∧ program.components = signed.toNat := by
  dsimp only
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, inherited,
      closed, original, result, after, baseRanges, done, allRanges, next, final, graph,
      checks, reads, post, afterFrame, afterFits, afterKnown, resultAvailable, law,
      nextReady, nextProfile, nextHistory, resultClosed, nodeFields, valueFields⟩ :=
    SourceSynthesisCurrentComputedWidthSharedCompletion.accepted lib query signed expression returned
      budget formulas solver
  have mappedBuilt : InternedFreshOrdinaryConstruction.build (mapSyntax literal expression)
      [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  refine ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame, inherited,
    closed, original, result, after, baseRanges, done, allRanges, next, final, graph,
    checks, reads, post, afterFrame, afterFits, afterKnown, resultAvailable, law,
    nextReady, nextProfile, nextHistory, resultClosed, nodeFields, valueFields, ?_⟩
  intro ambient term accepted
  have originalMember := (law ambient term).1
    (Eq.mp (meaning_decider_eq _ _ formulas solver ambient result term) accepted)
  have publicMember : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient value term :=
    Eq.mp (meaning_decider_eq _ _ formulas solver ambient value term) originalMember
  have sourceAccepted : InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver)
      [] (mapSyntax literal expression) term := by
    rw [← InternedGuardedExecution.closed_language (mapSyntax literal expression) value heap mappedBuilt
      (SourceEqualityPCSGuard.holds formulas solver) ambient]
    exact publicMember
  exact SourceSynthesisCurrentRootTyping.firstOrderRaw_typed formulas solver lib query signed expression
    returned term sourceAccepted

end MicroCFTA.SourceSynthesisCurrentComputedWidthTypedSharedCompletion

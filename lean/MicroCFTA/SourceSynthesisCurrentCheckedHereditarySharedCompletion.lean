import MicroCFTA.SourceSynthesisCurrentCallerInitialization
import MicroCFTA.SourceSynthesisProgramTypeFieldConstruction
import MicroCFTA.SourceSynthesisOriginalSharedRankCompletion
import MicroCFTA.SourceSynthesisHereditarySharedOuterTraversal
import MicroCFTA.SourceCurrentSharedOuterInitialLiteralRanges
import MicroCFTA.SourceCurrentAllocatedSharedPartialChecksFromRanges
import MicroCFTA.SourceCurrentAllocatedSharedPartialRangesFromChecks

/-!
# Current checked shared completion with complete Type fields

One current initializer fixes the build, cache, inventory, and caller.
Current source facts derive every initial Type and memo certificate.
One rank producer supplies the same completed endpoint at larger outer fuel.
The actual computed Room condition remains explicit.
-/
namespace MicroCFTA.SourceSynthesisCurrentCheckedHereditarySharedCompletion
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
open SourceCurrentAllocatedNativeResourceForecast (Room)
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
local notation "cover" => SourceCurrentInitialSelectionForecast.cover
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Current source success retains the full initializer and one checked hereditary return. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (bits budget : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
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
            SharedReady (encodedLibrary lib) (initialShared after.checked after.merge) ∧
            GuardHeap (Origin (encodedLibrary lib)) after.checked.native.machine.heap ∧
            History (encodedLibrary lib) literal after ∧ result.free = [] ∧
            NodeFields (encodedLibrary lib) literal request result ∧
            ValueFields (Origin (encodedLibrary lib)) literal result := by
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, inherited, closed, original⟩ :=
    SourceSynthesisCurrentCallerInitialization.accepted lib query signed expression returned
      (bits + 2) Cache.emptyState Cache.empty_valid formulas solver
  obtain ⟨sourceMuStored, sourceFields⟩ := SourceSynthesisProgramTypeFieldConstruction.current_root_fields
    lib query signed expression returned value heap built
  let before := caller (bits + 2) cache heap
  let request : NodeRequest := ⟨emptyValue cache, value⟩
  let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
  let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request before
  let need := phaseNeed budget first (seed heap)
  have ready : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited := by
    change SourceEqualityConstraintAllocation.Ready _ (emptyValue cache)
    rw [emptySame]
    exact inherited
  have frame : Frame formulas solver (inventory (ordinarySymbols expression) value heap built) before.checked :=
    SourceCurrentConstructedOuterInitial.frame formulas solver
      (inventory (ordinarySymbols expression) value heap built) ⟨heap, Cache.emptyState⟩
      (operations cache) (ordinarySymbols expression) value built context.ready rfl
  have fits : Fits (seed heap).2 before.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap :=
    SourceCurrentConjunctionGuardUniverse.initial heap facts
  have typeReady : TypeReady (encodedLibrary lib) (cold (bits + 2) heap (operations cache)) :=
    ⟨context.ready.good,
      SourceEqualityRequiredSemanticCache.constructed (ordinarySymbols expression) value heap built,
      SourceCurrentAllocatedNativeScopeCache.initial_scoped (bits + 2) ⟨heap, Cache.emptyState⟩,
      SourceRecursiveIntersectionNative.idle_initial _,
      SourceCurrentHereditaryNativeUniversalStore.initial (Origin (encodedLibrary lib))
        ⟨heap, Cache.emptyState⟩ (operations cache) sourceMuStored⟩
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryCosts.closed_heap (ordinarySymbols expression)
  have typedState : SharedReady (encodedLibrary lib) (initialShared before.checked before.merge) :=
    SourceSynthesisNativeTypeSharedState.initial (encodedLibrary lib) before.checked before.merge
      typeReady costs (SourceCurrentMemoMergeEffects.stored_empty heap)
      (SourceCurrentHereditaryMerge.stored_empty (Origin (encodedLibrary lib)))
  have profile : GuardHeap (Origin (encodedLibrary lib)) heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentConstrainedCapGuardExecution.closed_heap (Origin (encodedLibrary lib)) (ordinarySymbols expression)
  have history : History (encodedLibrary lib) literal before :=
    SourceSynthesisHereditaryClosedMemo.initial (encodedLibrary lib) literal (checked (bits + 2) cache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  have normal : SourceCurrentRequiredUnionNormal.UnionNormal heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentRequiredUnionNormal.build (ordinarySymbols expression) [] empty SourceCurrentRequiredUnionNormal.empty
  have supported : SourceCurrentNativeRequestPositivePositions.Support heap before.checked.native :=
    ⟨FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩
  have causal : SourceCurrentNativeMuPublication.History empty heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentNativeMuPublication.closed_history (ordinarySymbols expression)
  have merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) before.merge :=
    SourceCurrentConstrainedCapMemoMerge.stored_empty _
  have positiveMemo : SourceCurrentMergePositivePosition.Support before.merge :=
    SourceCurrentMergePositivePosition.support_empty
  have writers : SourceCurrentSharedResourceParentWriters.Origins formulas solver before :=
    SourceCurrentSharedResourceParentWriters.initial formulas solver (checked (bits + 2) cache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  have stored : SourceCurrentSharedOuterClosedInputs.NodeStored before :=
    SourceCurrentSharedOuterClosedInputs.initial (checked (bits + 2) cache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  have nodeIdle : ∀ chosen owner, before.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩ := by
    intro chosen owner impossible
    cases impossible
  have edgeIdle : SourceCurrentSharedOuterEdgeIdle.EdgeIdle before :=
    SourceCurrentSharedOuterEdgeIdle.initial (checked (bits + 2) cache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  refine ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context, facts, available,
    roles, growth, issued, origins, identity, emptySame, inherited, closed, original, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, done⟩ := SourceCurrentSharedOuterRankAdequacy.initial_node_call
    formulas solver (g := need) (s := need) (r := need) (e := need) (p := need) (h := need)
    (m := need) (c := need) (n := need) (budget := budget) (request := request) (seed heap)
    context frame fits known ⟨ready, available⟩ room normal supported causal merged positiveMemo writers
    stored closed nodeIdle edgeIdle (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have rootRoom : Room bits (forecast budget first (seed heap)).2 :=
    room.mono (SourceCurrentInitialSelectionForecast.cover_ge _ _)
  obtain ⟨next, final, graph, reads, post, afterFrame, afterFits, afterKnown,
      resultAvailable, law, nextReady, nextProfile, nextHistory, resultClosed, resultFields⟩ :=
    SourceSynthesisHereditarySharedOuterTraversal.nodeCall_fields (encodedLibrary lib) literal formulas solver (seed heap)
      (request := request) context frame fits known typedState profile history ready available closed
      (Or.inr sourceFields) rootRoom (done output.1 (Nat.le_refl _))
  have checkedBase : SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
      output.1 need need need need need need need need need budget request before :=
    SourceCurrentSharedOuterInitialLiteralRanges.node_call formulas solver output.1 (seed heap)
      context frame fits known ready available rootRoom
  have checkedGraph := SourceCurrentAllocatedSharedPartialChecksFromRanges.node_call
    checkedBase (done output.1 (Nat.le_refl _)) graph
  have checkedRuns : ∀ fuel, output.1 ≤ fuel →
      SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
        fuel need need need need need need need need need budget request before := by
    intro fuel enough
    exact SourceCurrentAllocatedSharedPartialRangesFromChecks.node_call
      (graph := graph) checkedGraph (done fuel enough)
  exact ⟨result, after, checkedBase, done, checkedRuns, next, final, graph, checkedGraph,
    reads, post, afterFrame, afterFits, afterKnown, resultAvailable, law, nextReady, nextProfile,
    nextHistory, resultClosed, resultFields, resultFields.program sourceFields⟩

end MicroCFTA.SourceSynthesisCurrentCheckedHereditarySharedCompletion

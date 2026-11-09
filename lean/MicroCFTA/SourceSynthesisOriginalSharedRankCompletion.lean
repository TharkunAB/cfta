import MicroCFTA.SourceSynthesisOriginalCallerInitialization
import MicroCFTA.SourceCurrentConstructedOuterInitial
import MicroCFTA.SourceCurrentSharedOuterRankAdequacy

/-!
# Original cold shared worker completion under computed capacity

Accepted source input derives the actual build and caller. The empty
tables derive their support, closure, writer, and idle invariants.
The shared outer rank supplies the worker and lower bounds.
No successful execution or future invariant is an input.

The theorem retains one explicit Room test for the computed initial
forecast. This test can be very conservative. The theorem does not prove
that native fixed-width execution satisfies it. It does not bound the
complete enumeration driver or establish native demand correspondence.
-/
namespace MicroCFTA.SourceSynthesisOriginalSharedRankCompletion
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedSharedPartialWorker (nodeCall)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue checked operations inventory globals)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "envelope" => SourceCurrentSharedOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
local notation "cover" => SourceCurrentInitialSelectionForecast.cover
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Actual initial record reads determine the numeric profile and finite guard list. -/
def seed (heap : State Symbol Guard) : List Guard × Profile :=
  (SourceCurrentConjunctionGuardUniverse.guards heap,
    ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)

/-- Original input constructs a stable shared worker return under its computed capacity test. -/
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
        (∀ fuel, output.1 ≤ fuel →
          nodeCall fuel need need need need need need need need need budget request
            (caller (bits + 2) cache heap) = .done result after) ∧
        Available after.checked.native.machine.heap result ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  obtain ⟨fields, cache, value, heap, built, prepared, context, facts, available, _roles,
      _growth, _history, _identity, emptySame, inherited, closed, _original⟩ :=
    SourceSynthesisOriginalCallerInitialization.accepted lib query signed expression returned (bits + 2)
      Cache.emptyState Cache.empty_valid formulas solver
  let before := caller (bits + 2) cache heap
  let request : NodeRequest := ⟨emptyValue cache, value⟩
  let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
  let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request before
  let need := phaseNeed budget first (seed heap)
  have frame : Frame formulas solver (inventory (ordinarySymbols expression) value heap built) before.checked :=
    SourceCurrentConstructedOuterInitial.frame formulas solver
      (inventory (ordinarySymbols expression) value heap built) ⟨heap, Cache.emptyState⟩
      (operations cache) (ordinarySymbols expression) value built context.ready rfl
  have fits : Fits (seed heap).2 before.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (seed heap).1) heap :=
    SourceCurrentConjunctionGuardUniverse.initial heap facts
  have ready : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited := by
    change SourceEqualityConstraintAllocation.Ready _ (emptyValue cache)
    rw [emptySame]
    exact inherited
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
  have origins : SourceCurrentSharedResourceParentWriters.Origins formulas solver before :=
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
  refine ⟨fields, cache, value, heap, built, prepared, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, done⟩ := SourceCurrentSharedOuterRankAdequacy.initial_node_call
    formulas solver (g := need) (s := need) (r := need) (e := need) (p := need) (h := need)
    (m := need) (c := need) (n := need) (budget := budget) (request := request) (seed heap)
    context frame fits known ⟨ready, available⟩ room normal supported causal merged positiveMemo origins
    stored closed nodeIdle edgeIdle (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have rootRoom : Room bits (forecast budget first (seed heap)).2 :=
    room.mono (SourceCurrentInitialSelectionForecast.cover_ge _ _)
  obtain ⟨_next, _final, _graph, _reads, _post, _frame, _fits, _known, outputAvailable, law⟩ :=
    SourceCurrentSharedOuterInitialActual.node_call formulas solver output.1 (request := request) (seed heap)
      context frame fits known ready available rootRoom (done output.1 (Nat.le_refl _))
  exact ⟨result, after, done, outputAvailable, law⟩

end MicroCFTA.SourceSynthesisOriginalSharedRankCompletion

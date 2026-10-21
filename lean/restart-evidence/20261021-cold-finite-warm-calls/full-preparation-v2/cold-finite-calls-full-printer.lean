import MicroCFTA.SourceCurrentFiniteWarmCalls
import MicroCFTA.SourceCurrentColdRankCapacity
import MicroCFTA.FormulaExecutable

namespace MicroCFTA.SourceCurrentColdFiniteWarmCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialWorker (nodeCall)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-!
# Constructed finite calls at one mathematical width

Construct the source heap before choosing the width for all rounds.
Create one caller at that width and retain its actual finite trace.
The empty inherited payload gives exact finite-term language equivalence.
This theorem does not include withoutRedundantEdges or assert convergence.
-/

/-- Covered closed construction supplies one finite trace and its final language. -/
theorem constructed_node_calls
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {initial finalCache : Cache.State SourceEqualityPartialConstraintKey.Key}
    {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initial finalCache originals)
    (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ originals)
    (budget rounds : Nat) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
    let seed : List Guard × Profile := (SourceEqualityConstraintOrigins.guards expression,
      ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)
    let bits := SourceCurrentParentInitialRoom.roomBits
      (SourceCurrentFiniteRoundForecast.stage budget seed rounds).2
    let fuels := SourceCurrentFiniteRoundForecast.fuelBounds budget rounds seed
    let inherited := SourceCurrentAllocatedPartialInitialization.emptyValue finalCache
    let before := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) finalCache heap
    ∃ trace : Fin (rounds + 1) → Node × Caller (bits + 2),
      trace 0 = (value, before) ∧
      (∀ index : Fin rounds,
        nodeCall fuels.1
          fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 budget
          ⟨inherited, (trace index.castSucc).1⟩ (trace index.castSucc).2 =
            .done (trace index.succ).1 (trace index.succ).2) ∧
      Available (trace (Fin.last rounds)).2.checked.native.machine.heap (trace (Fin.last rounds)).1 ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (@SourceEqualityPCSGuard.holds FullSyntax.Formula
          FormulaExecutable.formulaDecidableEq formulas solver) ambient value term ↔
          InternedGuardedLanguage.meaning (@SourceEqualityPCSGuard.holds FullSyntax.Formula
            FormulaExecutable.formulaDecidableEq formulas solver) ambient
            (trace (Fin.last rounds)).1 term
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
  let bits := SourceCurrentParentInitialRoom.roomBits
    (SourceCurrentFiniteRoundForecast.stage budget seed rounds).2
  let fuels := SourceCurrentFiniteRoundForecast.fuelBounds budget rounds seed
  let inherited := SourceCurrentAllocatedPartialInitialization.emptyValue finalCache
  let before := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) finalCache heap
  let inventory := SourceCurrentAllocatedPartialInitialization.inventory expression value heap built
  change ∃ trace : Fin (rounds + 1) → Node × Caller (bits + 2),
    trace 0 = (value, before) ∧
    (∀ index : Fin rounds,
      nodeCall fuels.1
        fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 budget
        ⟨inherited, (trace index.castSucc).1⟩ (trace index.castSucc).2 =
          .done (trace index.succ).1 (trace index.succ).2) ∧
    Available (trace (Fin.last rounds)).2.checked.native.machine.heap (trace (Fin.last rounds)).1 ∧
    ∀ ambient term,
      InternedGuardedLanguage.meaning (@SourceEqualityPCSGuard.holds FullSyntax.Formula
        FormulaExecutable.formulaDecidableEq formulas solver) ambient value term ↔
        InternedGuardedLanguage.meaning (@SourceEqualityPCSGuard.holds FullSyntax.Formula
          FormulaExecutable.formulaDecidableEq formulas solver) ambient
          (trace (Fin.last rounds)).1 term
  obtain ⟨context, _identity, same, inheritedReady, available, closed, _original⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed (bits + 2) history valid
      expression covered value heap built formulas solver
  have startContext : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before
      SourceCurrentAllocatedPartialInitialization.globals := context
  have ready : SourceEqualityConstraintAllocation.Ready
      before.checked.operations.constraints inherited := by
    change SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints
      (SourceCurrentAllocatedPartialInitialization.emptyValue finalCache)
    rw [same]
    exact inheritedReady
  have frame : SourceCurrentConstrainedCapGeneratedQueryResources.Frame
      formulas solver inventory before.checked :=
    SourceCurrentConstructedOuterInitial.frame formulas solver inventory
      ⟨heap, Cache.emptyState⟩ (SourceCurrentAllocatedPartialInitialization.operations finalCache)
      expression value built startContext.ready
      (SourceCurrentAllocatedPartialInitialization.inventory_source expression value heap built)
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  have fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 before.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      before.checked.native.machine.heap := physicalCarrier
  have inputs : SourceCurrentOuterPrefixInvariants.NodeReady before ⟨inherited, value⟩ :=
    ⟨ready, available⟩
  have normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap := by
    change SourceCurrentRequiredUnionNormal.UnionNormal heap
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentRequiredUnionNormal.source expression
  have supported : SourceCurrentNativeRequestPositivePositions.Support
      before.checked.native.machine.heap before.checked.native :=
    ⟨FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩
  have causal : SourceCurrentNativeMuPublication.History empty before.checked.native.machine.heap := by
    change SourceCurrentNativeMuPublication.History empty heap
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
  have nodeIdle : ∀ chosen owner, before.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩ := by
    intro chosen owner impossible
    cases impossible
  have edgeIdle : SourceCurrentOuterEdgeIdle.EdgeIdle before :=
    SourceCurrentOuterEdgeIdle.initial
      (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) finalCache heap)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  obtain ⟨trace, first, steps, finalAvailable, law⟩ :=
    SourceCurrentFiniteWarmCalls.node_calls formulas solver budget rounds seed
      startContext frame fits carrier inputs normal supported causal merged positiveMemo
      origins stored closed nodeIdle edgeIdle
  refine ⟨trace, first, steps, finalAvailable, ?_⟩
  intro ambient term
  apply ((law ambient term).2 ?_).symm
  obtain ⟨_emptyIdentity, emptyLive⟩ :=
    SourceCurrentAllocatedPartialInitialization.emptyValue_live finalCache
  simp [inherited, emptyLive, SourceEqualityConstraintAllocation.Value.payload,
    SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

end MicroCFTA.SourceCurrentColdFiniteWarmCalls

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentColdFiniteWarmCalls.constructed_node_calls
#print MicroCFTA.SourceCurrentColdFiniteWarmCalls.constructed_node_calls
#print axioms MicroCFTA.SourceCurrentColdFiniteWarmCalls.constructed_node_calls

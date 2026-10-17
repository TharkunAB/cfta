import MicroCFTA.SourceCurrentAllocatedMergeNumericReplay
import MicroCFTA.SourceEqualityPCSNativeEdge
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.InternedFreshOrdinaryCosts
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.AllocatedMergeNumericIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedMergeGraph (State Memo Call top)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentMemoMergeUniformNumeric (workFuel selectionFuel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def seedEqualities : Option EqualityNormalize.Constraints := some [[[0, 0], [0, 1]]]
private def seedBuild := SourceEqualityConstraintAllocation.construct seedEqualities Cache.emptyState
private def seedValue : SourceEqualityConstraintAllocation.Value := match seedBuild.1 with
  | .ok value => value
  | .error _ => .contradiction
private def seedState := SourceEqualityConstraintMemoAllocation.initial seedBuild.2
private def preparedOperations := (SourceEqualityConstraintMemoAllocation.descend seedValue 0 seedState).2
private def operations := SourceEqualityMkEdgeAllocation.emptyField preparedOperations

private theorem seed_cached : SourceEqualityGuardReadback.Cached seedEqualities := by
  have actual : EqualityNormalize.mkEqConstraints 4 [[[0, 0], [0, 1]]] = .normalized [[[0, 0], [0, 1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized actual
private theorem seed_constructed : seedBuild.1 = .ok seedValue := by cbv
private theorem prepared_valid : SourceEqualityConstraintMemoAllocation.Valid preparedOperations := by
  obtain ⟨value, cache, built, cacheValid, ready, _steps, _read, _classes⟩ :=
    SourceEqualityConstraintAllocation.construct_complete seedEqualities seed_cached Cache.emptyState Cache.empty_valid
  have same : value = seedValue := Except.ok.inj ((congrArg Prod.fst built).symm.trans seed_constructed)
  subst value
  have cacheSame : cache = seedBuild.2 := (congrArg Prod.snd built).symm
  subst cache
  exact (SourceEqualityConstraintMemoAllocation.descend_correct seedValue 0 seedState
    (SourceEqualityConstraintMemoAllocation.initial_valid _ cacheValid) ready).1

private def topBefore : State := ⟨empty, preparedOperations⟩
private def topResult := run (makeEdge ("top", .top) top []) topBefore.heap
private def topAfter : State := ⟨topResult.2, SourceEqualityMkEdgeAllocation.emptyField preparedOperations⟩

/-- Literal Top work allocates a fresh empty field and retains the populated descent table. -/
theorem top_allocates :
    SourceCurrentAllocatedMergeWorker.execute (fun _ => true) 1 0
      (.topRow ("top", .top) []) topBefore SourceCurrentMemoMergeGraph.empty =
      .done topResult.1 topAfter SourceCurrentMemoMergeGraph.empty ∧
    topAfter.equality.constraints.next = topBefore.equality.constraints.next + 1 ∧
    topAfter.heap.edges.next = topBefore.heap.edges.next + 1 ∧
    topAfter.equality.combinations = topBefore.equality.combinations ∧
    topAfter.equality.descents = topBefore.equality.descents ∧
    (topAfter.equality.descents (seedValue.identity, 0)).isSome = true := by
  have actual := SourceCurrentAllocatedMergeGraph.Run.topRow (clear := fun _ => true)
    ("top", .top) [] topBefore SourceCurrentMemoMergeGraph.empty
  have old : SourceCurrentMemoMergeWorker.execute (fun _ => true) top 1 0
      (SourceCurrentAllocatedMergeGraph.erase (.topRow ("top", .top) [])) topBefore.heap
      SourceCurrentMemoMergeGraph.empty = .done topResult.1 topAfter.heap SourceCurrentMemoMergeGraph.empty := rfl
  exact ⟨SourceCurrentAllocatedMergeNumericReplay.run_replay actual 1 0 old,
    (by cbv), (by cbv), rfl, rfl, (by cbv)⟩

private def leaf (symbol : String) : InternedNestedConstruction.Syntax Symbol Guard :=
  .node [.mk (symbol, .top) top []]
private def recursivePlan : InternedNestedConstruction.Syntax Symbol Guard :=
  .binder true (.node [.mk ("step", .top) top [.var 0], .mk ("stop", .top) top []])
private def expression : InternedNestedConstruction.Syntax Symbol Guard :=
  .node [.mk ("root", .top) top [recursivePlan], .mk ("root", .top) top [leaf "a"],
    .mk ("root", .top) top [.union [recursivePlan, leaf "b"]],
    .mk ("root", .top) top [leaf "c"], .mk ("root", .top) top [leaf "d"]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def before : State := ⟨heap, operations⟩
private def scalar := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next
  (InternedValueMassHeap.initialBound heap)
private theorem constructed : built = .done input heap := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, input, heap, done, InternedNestedConstruction.Outcome.state]
private theorem available : Available heap input :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result _ _ constructed
private theorem initial_ready : Ready before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, leaf, recursivePlan, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    preparedOperations prepared_valid
  refine ⟨semantic, ?_, loaded.1, ?_⟩
  · simpa only [built, heap] using InternedFreshOrdinaryCosts.closed_heap expression
  · intro key row found
    have same := guarded key row found
    rw [same]
    exact loaded.2.2
private theorem initial_fits : Fits scalar heap :=
  SourceCurrentMemoMergeResourceControl.initial heap _
    (InternedValueMassHeap.initial heap initial_ready.semantic.ready.semantic.1.normal.facts)

private def Completed : Prop := ∃ output after saved,
  Call (fun _ => true) input before SourceCurrentMemoMergeGraph.empty output after saved ∧
  SourceCurrentAllocatedMergeWorker.call (fun _ => true) (workFuel scalar) (selectionFuel scalar)
    input before SourceCurrentMemoMergeGraph.empty = .done output after saved ∧
  Effects before after ∧ SourceCurrentMemoMergeEffects.Stored after.heap saved ∧
  Available after.heap output ∧ Fits (workFuel scalar) after.heap ∧
  ∀ workExtra selectionExtra,
    SourceCurrentAllocatedMergeWorker.call (fun _ => true)
      (workFuel scalar + workExtra) (selectionFuel scalar + selectionExtra)
      input before SourceCurrentMemoMergeGraph.empty = .done output after saved
private theorem completed : Completed := by
  obtain ⟨output, after, saved, actual, done, effect, stored, result, _closed, fits, _mass, stable⟩ :=
    SourceCurrentAllocatedMergeNumericReplay.complete (fun _ => true) input before
      SourceCurrentMemoMergeGraph.empty scalar initial_ready
      (SourceCurrentMemoMergeEffects.stored_empty _) available initial_fits
  exact ⟨output, after, saved, actual, done, effect, stored, result, fits, stable⟩

/-- An initial mixed recursive five-row group constructs its own full allocated numeric return. -/
theorem recursive_large :
    built = .done input heap ∧
    (MergedSourceGrouping.groups (InternedEdgeResidency.nodeEdges input)).map List.length = [5] ∧
    (children input).any isMu = true ∧ (children input).any isUnion = true ∧ Completed :=
  ⟨constructed, (by cbv), (by cbv), (by cbv), completed⟩

/-- A new numeric call reuses the first actual returned full state and its retained first winner. -/
theorem cold_then_warm : ∃ output after saved,
    SourceCurrentAllocatedMergeWorker.call (fun _ => true) (workFuel scalar) (selectionFuel scalar)
      input before SourceCurrentMemoMergeGraph.empty = .done output after saved ∧
    Fits (workFuel scalar) after.heap ∧
    SourceCurrentAllocatedMergeWorker.call (fun _ => true) (workFuel (workFuel scalar))
      (selectionFuel (workFuel scalar)) input after saved = .done output after saved ∧
    (after.equality.descents (seedValue.identity, 0)).isSome = true := by
  obtain ⟨output, after, saved, actual, done, effect, stored, result, fits, _stable⟩ := completed
  obtain ⟨entry, found, same⟩ := actual.graph.present
  have hit : Call (fun _ => true) input after saved entry.result after saved := .hit found
  have warm := SourceCurrentAllocatedMergeNumericReplay.of_call hit (workFuel scalar)
    effect.ready.semantic effect.ready.costs stored (effect.keeps.available _ available) fits
  have present : (operations.descents (seedValue.identity, 0)).isSome = true := by cbv
  have retained : (after.equality.descents (seedValue.identity, 0)).isSome = true := by
    cases initial : operations.descents (seedValue.identity, 0) with
    | none => rw [initial] at present; cases present
    | some cell =>
        have later := effect.grows.descents (seedValue.identity, 0) cell initial
        rw [later]
        rfl
  rw [← same] at warm
  exact ⟨output, after, saved, done, fits, warm.1, retained⟩
end MicroCFTA.AllocatedMergeNumericIntegration

#print axioms MicroCFTA.AllocatedMergeNumericIntegration.top_allocates
#check @MicroCFTA.AllocatedMergeNumericIntegration.top_allocates
#print axioms MicroCFTA.AllocatedMergeNumericIntegration.recursive_large
#check @MicroCFTA.AllocatedMergeNumericIntegration.recursive_large
#print axioms MicroCFTA.AllocatedMergeNumericIntegration.cold_then_warm
#check @MicroCFTA.AllocatedMergeNumericIntegration.cold_then_warm

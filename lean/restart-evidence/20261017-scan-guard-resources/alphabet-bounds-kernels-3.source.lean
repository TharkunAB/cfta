import MicroCFTA.SourceCurrentConjunctionAlphabetBounds
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.EndpointMemoGateSource
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.AlphabetBoundsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) cached allocation
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by simpa only [expression, SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards,
      List.nil_append, List.append_nil] using member) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩

private theorem no_cap (depth : Nat) : ¬Cap depth value := by
  intro bounded
  cbv at bounded
  cases bounded with
  | plain _ annotated =>
      cases annotated with
      | mu _ _ _ _ body =>
          cases body with
          | node _ _ _ _ annotations _ =>
              have rejected := annotations _ List.mem_cons_self
              change SourceMemoGate.plain annotation = true at rejected
              have invalid : SourceMemoGate.plain annotation = false := by cbv
              rw [invalid] at rejected
              cases rejected



private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty

private theorem initial_frame (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Frame formulas solver inventory (before width) :=
  Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl

private theorem initial_context (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (caller width) EndpointMemoGateTrace.empty := by
  refine ⟨(initial width).1, (initial_frame width formulas solver).admitted,
    SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver _ _ _,
    SourceCurrentMemoMergeEffects.stored_empty _, ?_,
    SourceCurrentEmptinessMemo.empty_correct formulas solver heap, EndpointMemoGateTrace.empty_valid heap, ?_⟩
  · intro ambient key entry absent
    cases absent
  · change InternedFreshOrdinaryProbeHeap.Heap heap
    simpa only [heap, built] using InternedFreshOrdinaryProbeHeap.closed_heap expression


private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance


private def alphabet : List Guard := [annotation, SourceEqualityConstraintConstructors.top]
private theorem carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) heap := by
  have allowed : SourceEqualityAnnotationConstruction.Allowed (fun guard => guard ∈ alphabet) expression := by
    simp only [expression, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]
    repeat' first | exact List.mem_cons_self | constructor
  simpa only [heap, built] using SourceEqualityAnnotationConstruction.build
    (fun guard => guard ∈ alphabet) expression allowed [] empty (SourceEqualityAnnotationHeap.empty_heap _)

/-- A literal supplied alphabet constructs the full caller and remains fixed at its exact warm return. -/
theorem constructed_caller (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧
    ∃ answer after saved,
      SourceCurrentConjunctionMemo.Call 3 (caller width).fourth value
        (SourceCurrentAllocatedNativeEffects.physical (before width)) answer after saved ∧
      Frame formulas solver inventory (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) ∧
      SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory (caller width)
        (SourceCurrentAllocatedPartialState.advance (caller width)
          (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) saved (caller width).merge)
        EndpointMemoGateTrace.empty ∧
      Fits (SourceCurrentConjunctionAlphabetBounds.callerForecast alphabet 3 profile)
        (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver value answer ∧
      (SourceCurrentAllocatedPartialState.advance (caller width)
        (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) saved (caller width).merge).nodeResults =
        (caller width).nodeResults ∧
      (SourceCurrentAllocatedPartialState.advance (caller width)
        (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) saved (caller width).merge).edgeResults =
        (caller width).edgeResults ∧
      (SourceCurrentAllocatedPartialState.advance (caller width)
        (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) saved (caller width).merge).merge =
        (caller width).merge ∧
      (SourceCurrentAllocatedPartialState.advance (caller width)
        (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) saved (caller width).merge).fourth = saved ∧
      SourceCurrentEmptinessMemo.Extends (caller width).fourth saved ∧
      saved value.referenceOf = some (value, answer) ∧
      SourceCurrentConjunctionMemo.Call 3 saved value after answer after saved ∧
      (∀ work reader,
        SourceCurrentConjunctionWorklistResources.workerFuel alphabet 3
          (SourceCurrentConstrainedCapTargetForecast.scalar profile) ≤ work →
        SourceCurrentConjunctionWorklistResources.readerFuel alphabet 3
          (SourceCurrentConstrainedCapTargetForecast.scalar profile) ≤ reader →
        SourceCurrentConjunctionWorker.call work reader 3 (caller width).fourth value
          (SourceCurrentAllocatedNativeEffects.physical (before width)) = .done (answer, saved) after) := by
  obtain ⟨answer, after, saved, actual, returned, post, bounded, known, sound, nodes, edges, merge, fourth, done⟩ :=
    SourceCurrentConjunctionAlphabetBounds.caller_complete formulas solver alphabet inventory 3 value (caller width)
      EndpointMemoGateTrace.empty (initial_context width formulas solver)
      (initial_frame width formulas solver) profile (initial_fits width) (initial width).2.1 carrier
  have installed : saved value.referenceOf = some (value, answer) := by
    cases actual with
    | hit impossible => cases impossible
    | miss _ _ => simp only [SourceCurrentEmptinessMemo.insert, ite_true]
  have warm : SourceCurrentConjunctionMemo.Call 3 saved value after answer after saved := .hit installed
  exact ⟨no_cap, answer, after, saved, actual, returned, post, bounded, known, sound,
    nodes, edges, merge, fourth, post.fourthRetained, installed, warm, done⟩

/-- The produced carrier and context supply the second initial call with the same alphabet. -/
theorem constructed_two_calls (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ (answer : Bool) (after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula)
      (saved : SourceCurrentEmptinessMemo.Memo),
      SourceCurrentConjunctionMemo.Call 3 SourceCurrentEmptinessMemo.empty value
        (SourceCurrentAllocatedNativeEffects.physical (before width)) answer after saved ∧
      SourceCurrentConjunctionMemo.Call 3 saved value after answer after saved ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap ∧
      SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory (caller width)
        (SourceCurrentAllocatedPartialState.advance (caller width)
          (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) saved (caller width).merge)
        EndpointMemoGateTrace.empty ∧
      (∀ work reader,
        SourceCurrentConjunctionWorklistResources.workerFuel alphabet 3
          (SourceCurrentConstrainedCapTargetForecast.scalar
            (SourceCurrentConjunctionAlphabetBounds.callerForecast alphabet 3 profile)) ≤ work →
        SourceCurrentConjunctionWorklistResources.readerFuel alphabet 3
          (SourceCurrentConstrainedCapTargetForecast.scalar
            (SourceCurrentConjunctionAlphabetBounds.callerForecast alphabet 3 profile)) ≤ reader →
        SourceCurrentConjunctionWorker.call work reader 3 saved value after = .done (answer, saved) after) := by
  obtain ⟨answer, after, saved, actual, returned, post, bounded, known, _sound, _nodes, _edges, _merge, _fourth, _done⟩ :=
    SourceCurrentConjunctionAlphabetBounds.caller_complete formulas solver alphabet inventory 3 value (caller width)
      EndpointMemoGateTrace.empty (initial_context width formulas solver)
      (initial_frame width formulas solver) profile (initial_fits width) (initial width).2.1 carrier
  have installed : saved value.referenceOf = some (value, answer) := by
    cases actual with
    | hit impossible => cases impossible
    | miss _ _ => simp only [SourceCurrentEmptinessMemo.insert, ite_true]
  let middle := SourceCurrentAllocatedPartialState.advance (caller width)
    (SourceCurrentAllocatedQueryMemo.advancePhysical (before width) after) saved (caller width).merge
  have inputs : Available middle.checked.native.machine.heap value :=
    post.effects.keeps.available value (initial width).2.1
  obtain ⟨answer2, after2, saved2, actual2, _frame2, post2, _fits2, known2, _sound2,
      _nodes2, _edges2, _merge2, _fourth2, done2⟩ :=
    SourceCurrentConjunctionAlphabetBounds.caller_complete formulas solver alphabet inventory 3 value middle
      EndpointMemoGateTrace.empty post.context returned
      (SourceCurrentConjunctionAlphabetBounds.callerForecast alphabet 3 profile) bounded inputs known
  have exact_return : answer2 = answer ∧ after2 = after ∧ saved2 = saved := by
    cases actual2 with
    | hit found =>
        change saved value.referenceOf = _ at found
        rw [installed] at found
        have same := congrArg Prod.snd (Option.some.inj found)
        exact ⟨same.symm, rfl, rfl⟩
    | miss absent _ =>
        change saved value.referenceOf = none at absent
        rw [installed] at absent
        cases absent
  rcases exact_return with ⟨rfl, rfl, rfl⟩
  exact ⟨answer2, after2, saved2, actual, actual2, known2, post.trans post2, done2⟩

end MicroCFTA.AlphabetBoundsKernels
#check @MicroCFTA.AlphabetBoundsKernels.constructed_caller
#print axioms MicroCFTA.AlphabetBoundsKernels.constructed_caller
#check @MicroCFTA.AlphabetBoundsKernels.constructed_two_calls
#print axioms MicroCFTA.AlphabetBoundsKernels.constructed_two_calls

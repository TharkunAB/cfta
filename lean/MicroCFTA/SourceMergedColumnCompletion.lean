import MicroCFTA.SourceMergedCompleteEffects

/-!
# Finite general retained-column construction

Actual general selection supplies stable finite bounds. Recursive boundaries
use literal union construction. Other retained operands use the smaller
ordinary union before recursive merging. All results remain closed.
-/
namespace MicroCFTA.SourceMergedColumnCompletion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure work retainedColumn)
open MergedOrdinaryHeight
open SourceMergedCompleteEffects
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Stable actual selection returns original closed available operands. -/
theorem select_complete [DecidableEq Symbol] (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before inputs) (closed : ClosedValues inputs) :
    Complete (fun fuel => SourceMergedSelection.select clear fuel inputs) before
      (fun after retained => Values after retained ∧ ClosedValues retained ∧ ∀ value ∈ retained, value ∈ inputs) := by
  obtain ⟨bound, retained, after, done⟩ := SourceMergedSelectionCompletion.select_eventually clear inputs before semantic available closed
  have checked := SourceMergedSelectionLanguage.select_exact clear bound (fun _ _ => true) (fun _ _ => False)
    (fun _ _ _ => rfl) inputs before semantic available closed retained after (done bound (Nat.le_refl _))
  exact ⟨bound, retained, after, done, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

/-- Retained columns complete using recursive correctness only at their smaller ordinary height. -/
theorem retained_complete (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (smaller : ∀ value, height value ≤ limit → ∀ before, SemanticReady before → Available before value → value.free = [] →
      Complete (fun fuel => recurse fuel value) before ValueReady)
    (retained : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before retained) (closed : ClosedValues retained) (bounded : ∀ value ∈ retained, height value ≤ limit) :
    Complete (fun fuel => retainedColumn (recurse fuel) retained) before ValueReady := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values)
      (bounded : ∀ value ∈ values, height value ≤ limit) :
      Complete (fun fuel => if values.any recursiveBoundary then work (makeUnion values)
        else MergedColdMerge.bind (work (ordinaryUnion values)) (recurse fuel)) before ValueReady := by
    by_cases boundary : values.any recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact work_complete (makeUnion values) before ValueReady checked.1 checked.2
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have rows := SourceMergedCache.ordinary_rows values before semantic available closed
      have checked := SourceEqualityRequiredCache.node _ before semantic.ready rows.1 rows.2
      have effects : Effect before (run (ordinaryUnion values) before).2 :=
        ⟨checked.1, SourceEqualityRequiredSemanticCache.node _ before semantic rows.1 rows.2⟩
      have heightBound := ordinaryUnion_bound values before semantic.ready.semantic.1.normal.facts.coherent
        semantic.ready.semantic.1.normal.facts.linked (fun value member => (available value member).resident) limit bounded
      apply bind_complete _ _ before (fun after value => ValueReady after value ∧ height value ≤ limit) ValueReady
        (work_complete (ordinaryUnion values) before _ effects ⟨⟨checked.2.1, checked.2.2.1⟩, heightBound⟩)
      intro value after effects valid
      exact smaller value valid.2 after effects.2 valid.1.1 valid.1.2
  cases retained with
  | nil => exact branches [] available closed bounded
  | cons first rest =>
      cases rest with
      | nil => exact pure_complete first before semantic ValueReady ⟨available _ List.mem_cons_self, closed _ List.mem_cons_self⟩
      | cons second rest => exact branches (first :: second :: rest) available closed bounded

/-- Actual general selection completes before any retained-column constructor or recursive call. -/
theorem column_complete [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat) (clear : Guard → Bool)
    (smaller : ∀ value, height value ≤ limit → ∀ before, SemanticReady before → Available before value → value.free = [] →
      Complete (fun fuel => recurse fuel value) before ValueReady)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (bounded : ∀ value ∈ inputs, height value ≤ limit) :
    Complete (fun fuel => SourceMergedWorker.column (recurse fuel) clear fuel inputs) before ValueReady := by
  apply bind_complete _ _ before _ _ (select_complete clear inputs before semantic available closed)
  intro retained after effects selected
  exact retained_complete recurse limit smaller retained after effects.2 selected.1 selected.2.1
    (fun value member => bounded value (selected.2.2 value member))

end MicroCFTA.SourceMergedColumnCompletion

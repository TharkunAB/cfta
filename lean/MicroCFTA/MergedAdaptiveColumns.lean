import MicroCFTA.MergedAdaptiveEffects

/-!
# Column selection in the actual current cache

The comparison bound comes from the current physical inventory. Filtering,
identity removal, and the boundary decision run before the ordinary union's
recursive call. The recursive certificate is restricted by ordinary height.
-/
namespace MicroCFTA.MergedAdaptiveColumns
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open MergedPhysicalComparison MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalGroupColumns MergedPhysicalGroupColumnWorker MergedOrdinaryHeight
open MergedAdaptiveEffects Language

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- Use the proved complete pair inventory bound for the current source comparison. -/
def comparisonFuel (state : State Symbol Guard) (outputs inputs : List (Value Symbol Guard)) : Nat :=
  (inventory state inputs outputs).length * (inventory state inputs outputs).length

/-- Compute retained operands at the actual column-call state. -/
def kept [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (outputs inputs : List (Value Symbol Guard))
    (meaning : Guard → Term Symbol → Bool) (unconstrained : Edge (Value Symbol Guard) Symbol → Bool) : List (Value Symbol Guard) :=
  selected closedMu (MergedPhysicalGroupColumns.compare state outputs inputs meaning unconstrained
    (comparisonFuel state outputs inputs)) inputs

/-- Execute one retained column with a state-dependent recursive worker. -/
def retainedColumn [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (retained : List (Value Symbol Guard)) : Action Symbol Guard (Value Symbol Guard) :=
  match retained with
  | [single] => pure single
  | others => if others.any recursiveBoundary then work (makeUnion others)
    else bind (work (ordinaryUnion others)) recurse

/-- Actual comparison selection precedes all retained-column constructor effects. -/
def column [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool) (inputs : List (Value Symbol Guard)) :
    Action Symbol Guard (Value Symbol Guard) := fun state =>
  retainedColumn recurse (kept state outputs inputs meaning unconstrained) state

/-- The retained-column branches require recursive correctness only at the smaller height bound. -/
theorem retained_complete [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Context state outputs → Available state value →
      ∃ result after, recurse value state = some (result, after) ∧ Result state after outputs meaning [value] result)
    (retained : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state outputs)
    (available : Values state retained) (closed : ∀ value ∈ retained, value.free = [])
    (bounded : ∀ value ∈ retained, height value ≤ limit) :
    ∃ result after, retainedColumn recurse retained state = some (result, after) ∧
      Result state after outputs meaning retained result := by
  have branches (values : List (Value Symbol Guard)) (available : Values state values)
      (closed : ∀ value ∈ values, value.free = []) (bounded : ∀ value ∈ values, height value ≤ limit) :
      ∃ result after,
        (if values.any recursiveBoundary then work (makeUnion values) else bind (work (ordinaryUnion values)) recurse) state = some (result, after) ∧
        Result state after outputs meaning values result := by
    by_cases boundary : values.any recursiveBoundary = true
    · let result := run (makeUnion values) state
      have built := context.makeUnion state outputs values available
      refine ⟨result.1, result.2, by simp only [boundary, ↓reduceIte, work]; rfl,
        ⟨.work (makeUnion values) state outputs context built.1, built.2, ?_⟩⟩
      intro value member term accepted
      exact (makeUnion_actual state outputs context values available meaning term).2.2.mpr ⟨value, member, accepted⟩
    · have noBoundary : values.any recursiveBoundary = false := Bool.eq_false_iff.mpr boundary
      have ordinary := fun value member => ordinary_operand value (closed value member)
        (by simpa using (List.any_eq_false.mp noBoundary) value member)
      let union := run (ordinaryUnion values) state
      have built := ordinaryUnion_actual state outputs context values available ordinary meaning
      have extension := Extension.work (ordinaryUnion values) state outputs context built.1
      have bound := ordinaryUnion_bound values state context.facts.coherent context.facts.linked
        (fun value member => (available value member).resident) limit bounded
      obtain ⟨result, after, done, checked⟩ := smaller union.1 bound union.2 built.1 built.2.1
      refine ⟨result, after, ?_, ⟨extension.trans checked.extension, checked.available, ?_⟩⟩
      · simpa only [noBoundary, Bool.false_eq_true, ↓reduceIte, MergedAdaptiveEffects.bind, work, Option.bind_some] using done
      · intro value member term accepted
        exact checked.covers union.1 (List.mem_singleton_self _) term ((built.2.2 term).mpr ⟨value, member, accepted⟩)
  cases retained with
  | nil => exact branches [] available closed bounded
  | cons first rest =>
      cases rest with
      | nil =>
          refine ⟨first, state, rfl, ⟨.refl state outputs context, available first List.mem_cons_self, ?_⟩⟩
          intro value member term accepted
          simpa only [List.mem_singleton.mp member] using accepted
      | cons second tail => exact branches (first :: second :: tail) available closed bounded

/-- Current-state comparison, filtering, and all source column branches preserve every original operand language. -/
theorem column_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Context state outputs → Available state value →
      ∃ result after, recurse value state = some (result, after) ∧ Result state after outputs meaning [value] result)
    (inputs : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state outputs)
    (available : Values state inputs) (closed : ∀ value ∈ inputs, value.free = [])
    (bounded : ∀ value ∈ inputs, height value ≤ limit) :
    ∃ result after, column recurse outputs meaning unconstrained inputs state = some (result, after) ∧
      Result state after outputs meaning inputs result := by
  have subset := selected_subset closedMu (MergedPhysicalGroupColumns.compare state outputs inputs meaning unconstrained
    (comparisonFuel state outputs inputs)) inputs
  obtain ⟨result, after, done, checked⟩ := retained_complete recurse limit outputs meaning smaller
    (kept state outputs inputs meaning unconstrained) state context
    (fun value member => available value (subset value member))
    (fun value member => closed value (subset value member))
    (fun value member => bounded value (subset value member))
  refine ⟨result, after, done, ⟨checked.extension, checked.available, ?_⟩⟩
  intro value member term accepted
  obtain ⟨retained, included, accepted⟩ := (checked_selected_exact state outputs context inputs available meaning unconstrained clear
    (comparisonFuel state outputs inputs) term).mpr ⟨value, member, accepted⟩
  exact checked.covers retained included term accepted

end
end MicroCFTA.MergedAdaptiveColumns

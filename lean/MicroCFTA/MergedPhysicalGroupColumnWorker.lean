import MicroCFTA.MergedPhysicalGroupColumns

/-!
# The three physical merged-column branches

Singleton columns return their stored record. Recursive boundaries use the
repaired retained union. The remaining operands are ordinary or empty, so
their actual union has a smaller ordinary height than the enclosing root.
Only that smaller recursive merge call requires an induction hypothesis.
-/
namespace MicroCFTA.MergedPhysicalGroupColumnWorker
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalComparison MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalUnionTransport MergedPhysicalGroupCalls MergedPhysicalGroupEdges
open MergedPhysicalGroupColumns MergedOrdinaryHeight Language

/-- The actual ordinary union is exact when every operand is ordinary or empty. -/
theorem ordinaryUnion_actual [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (values : List (Value Symbol Guard)) (available : Values state values)
    (ordinary : ∀ value ∈ values, value = .empty ∨ ∃ entry edges depth free, value = .node entry edges depth free)
    (meaning : Guard → Term Symbol → Bool) :
    let result := run (ordinaryUnion values) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧
      ∀ term, EpsilonUnion.Accepts (graph result.2 meaning) result.1 term ↔
        ∃ value ∈ values, EpsilonUnion.Accepts (graph state meaning) value term := by
  let edges := values.flatMap nodeEdges
  let result := run (ordinaryUnion values) state
  have resident : Edges state edges := by
    intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact resident_edges state context.facts.linked value (available value present).resident edge included
  have built := context.makeNode state outputs edges resident
  have growth := (InternedConstructorTemplates.run_correct (ordinaryUnion values) state context.facts.coherent.valid).2
  refine ⟨built.1, built.2, ?_⟩
  intro term
  have common : EpsilonUnion.Accepts (graph result.2 meaning) result.1 term ↔
      ∃ value ∈ values, EpsilonUnion.Accepts (graph result.2 meaning) value term := by
    change EpsilonUnion.Accepts (graph result.2 meaning) (run (makeNode edges) state).1 term ↔ _
    rw [makeNode_exact state result.2 context.facts edges resident meaning term]
    constructor
    · rintro ⟨edge, member, accepted⟩
      obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
      rcases ordinary value included with same | ⟨entry, own, depth, free, same⟩
      · subst value; simp [nodeEdges] at present
      · subst value
        exact ⟨_, included, (node_exact result.2 meaning entry own depth free term).mpr ⟨edge, present, accepted⟩⟩
    · rintro ⟨value, included, accepted⟩
      rcases ordinary value included with same | ⟨entry, own, depth, free, same⟩
      · subst value; exact False.elim (empty_rejects result.2 meaning term accepted)
      · subst value
        obtain ⟨edge, present, accepted⟩ := (node_exact result.2 meaning entry own depth free term).mp accepted
        exact ⟨edge, List.mem_flatMap.mpr ⟨_, included, present⟩, accepted⟩
  exact common.trans (exists_congr fun value => and_congr_right fun member =>
    accepts_stable state result.2 outputs context growth meaning value (available value member) term)

/-- Execute the source branches after comparison and ordered identity filtering. -/
def column (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (retained : List (Value Symbol Guard)) : Work Symbol Guard (Value Symbol Guard) :=
  match retained with
  | [single] => .pure single
  | others => if others.any recursiveBoundary then makeUnion others else (ordinaryUnion others).bind merge

/-- The column worker needs recursive correctness only below the enclosing ordinary layer. -/
theorem column_correct [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (retained : List (Value Symbol Guard)) (limit : Nat)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (recursiveCalls : ∀ value, height value ≤ limit → CallLaw merge (fun value => [value]) value outputs meaning)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (available : Values state retained) (closed : ∀ value ∈ retained, value.free = [])
    (bounded : ∀ value ∈ retained, height value ≤ limit) :
    let result := run (column merge retained) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧ Covers state result.2 meaning retained result.1 := by
  have branches (values : List (Value Symbol Guard)) (available : Values state values)
      (closed : ∀ value ∈ values, value.free = []) (bounded : ∀ value ∈ values, height value ≤ limit) :
      let result := run (if values.any recursiveBoundary then makeUnion values else (ordinaryUnion values).bind merge) state
      Context result.2 outputs ∧ Available result.2 result.1 ∧ Covers state result.2 meaning values result.1 := by
    by_cases boundary : values.any recursiveBoundary = true
    · simp only [boundary, ↓reduceIte]
      have built := context.makeUnion state outputs values available
      refine ⟨built.1, built.2, ?_⟩
      intro value member term accepted
      exact (makeUnion_actual state outputs context values available meaning term).2.2.mpr ⟨value, member, accepted⟩
    · have clear : values.any recursiveBoundary = false := Bool.eq_false_iff.mpr boundary
      have ordinary := fun value member => ordinary_operand value (closed value member)
        (by simpa using (List.any_eq_false.mp clear) value member)
      let union := run (ordinaryUnion values) state
      have built := ordinaryUnion_actual state outputs context values available ordinary meaning
      have smaller := ordinaryUnion_bound values state context.facts.coherent context.facts.linked
        (fun value member => (available value member).resident) limit bounded
      have merged := recursiveCalls union.1 smaller union.2 built.1 (by
        intro value member
        rw [List.mem_singleton.mp member]
        exact built.2.1)
      simp only [clear, Bool.false_eq_true, ↓reduceIte, run_bind]
      refine ⟨merged.1, merged.2.1, ?_⟩
      intro value member term accepted
      exact merged.2.2 union.1 (List.mem_singleton_self _) term ((built.2.2 term).mpr ⟨value, member, accepted⟩)
  cases retained with
  | nil => exact branches [] available closed bounded
  | cons first rest =>
      cases rest with
      | nil =>
          refine ⟨context, available first List.mem_cons_self, ?_⟩
          intro value member term accepted
          rw [List.mem_singleton.mp member] at accepted
          exact accepted
      | cons second tail => exact branches (first :: second :: tail) available closed bounded

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- The current physical comparison, filter, and repaired column worker cover the original column. -/
theorem checked_column_correct [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (inputs : List (Value Symbol Guard)) (available : Values state inputs)
    (closed : ∀ value ∈ inputs, value.free = []) (bounded : ∀ value ∈ inputs, height value ≤ limit)
    (meaning : Guard → Term Symbol → Bool) (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true) (fuel : Nat)
    (recursiveCalls : ∀ value, height value ≤ limit → CallLaw merge (fun value => [value]) value outputs meaning) :
    let retained := selected closedMu (MergedPhysicalGroupColumns.compare state outputs inputs meaning unconstrained fuel) inputs
    let result := run (column merge retained) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧ Covers state result.2 meaning inputs result.1 := by
  let retained := selected closedMu (MergedPhysicalGroupColumns.compare state outputs inputs meaning unconstrained fuel) inputs
  have subset := selected_subset closedMu (MergedPhysicalGroupColumns.compare state outputs inputs meaning unconstrained fuel) inputs
  have checked := column_correct merge retained limit outputs meaning recursiveCalls state context
    (fun value member => available value (subset value member))
    (fun value member => closed value (subset value member))
    (fun value member => bounded value (subset value member))
  refine ⟨checked.1, checked.2.1, ?_⟩
  intro value member term accepted
  obtain ⟨retainedValue, kept, accepted⟩ :=
    (checked_selected_exact state outputs context inputs available meaning unconstrained clear fuel term).mpr ⟨value, member, accepted⟩
  exact checked.2.2 retainedValue kept term accepted

end
end MicroCFTA.MergedPhysicalGroupColumnWorker

import MicroCFTA.MergedPhysicalGroup
import MicroCFTA.MergedAlternativesSubsumption

/-!
# Retained physical child columns

The source keeps every closed Mu operand. It removes another operand only
after a successful comparison with a kept Mu. Ordered identity removal and
actual union construction then preserve the complete column language.
-/
namespace MicroCFTA.MergedPhysicalGroupColumns
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedUnionRetention
open MergedPhysicalComparison MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges MergedOrdinaryHeight Language

/-- The recursive filter includes exactly closed Mu records. -/
def closedMu : Value Symbol Guard → Bool
  | value@(.mu ..) => value.free.isEmpty
  | _ => false

/-- Execute recursive retention followed by source first-identity duplicate removal. -/
def selected (recursive : Value Symbol Guard → Bool) (compare : Value Symbol Guard → Value Symbol Guard → Bool)
    (inputs : List (Value Symbol Guard)) : List (Value Symbol Guard) :=
  distinctNodes (inputs.filter fun child => recursive child || !((inputs.filter recursive).any fun wide => compare wide child))

/-- Every selected record is one of the actual original operands. -/
theorem selected_subset (recursive : Value Symbol Guard → Bool) (compare : Value Symbol Guard → Value Symbol Guard → Bool)
    (inputs : List (Value Symbol Guard)) (value : Value Symbol Guard) (member : value ∈ selected recursive compare inputs) :
    value ∈ inputs := (List.mem_filter.mp (distinctNodes_member _ value member)).1

/-- The normalized filter retains exactly the source's recursive-or-uncovered predicate. -/
theorem selected_member (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (recursive : Value Symbol Guard → Bool) (compare : Value Symbol Guard → Value Symbol Guard → Bool)
    (inputs : List (Value Symbol Guard)) (available : Values state inputs) (value : Value Symbol Guard) :
    value ∈ selected recursive compare inputs ↔
      MergedAlternativesSubsumption.Retained (fun value => recursive value = true) (fun wide narrow => compare wide narrow = true) inputs value := by
  have normalized : value ∈ selected recursive compare inputs ↔
      value ∈ inputs.filter (fun child => recursive child || !((inputs.filter recursive).any fun wide => compare wide child)) := by
    exact ⟨distinctNodes_member _ value,
      distinctNodes_retains state facts.coherent _ (fun child member => (available child (List.mem_filter.mp member).1).resident) value⟩
  rw [normalized]
  simp only [List.mem_filter, Bool.or_eq_true, MergedAlternativesSubsumption.Retained,
    Bool.not_eq_true', ← Bool.not_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨member, recursive | uncovered⟩
    · exact ⟨member, Or.inl recursive⟩
    · exact ⟨member, Or.inr (fun ⟨wide, member, rec, covers⟩ => uncovered ⟨wide, ⟨member, rec⟩, covers⟩)⟩
  · rintro ⟨member, recursive | uncovered⟩
    · exact ⟨member, Or.inl recursive⟩
    · exact ⟨member, Or.inr (fun ⟨wide, ⟨member, rec⟩, covers⟩ => uncovered ⟨wide, member, rec, covers⟩)⟩

/-- Successful physical comparisons suffice to prove the exact selected column language. -/
theorem selected_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (meaning : Guard → Term Symbol → Bool) (recursive : Value Symbol Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → Bool)
    (inputs : List (Value Symbol Guard)) (available : Values state inputs)
    (sound : ∀ wide ∈ inputs, ∀ narrow ∈ inputs, compare wide narrow = true →
      ∀ term, EpsilonUnion.Accepts (graph state meaning) narrow term → EpsilonUnion.Accepts (graph state meaning) wide term)
    (term : Term Symbol) :
    (∃ value ∈ selected recursive compare inputs, EpsilonUnion.Accepts (graph state meaning) value term) ↔
      ∃ value ∈ inputs, EpsilonUnion.Accepts (graph state meaning) value term := by
  constructor
  · rintro ⟨value, member, accepted⟩
    exact ⟨value, selected_subset recursive compare inputs value member, accepted⟩
  · rintro ⟨value, member, accepted⟩
    by_cases retained : recursive value = true ∨ ¬∃ wide ∈ inputs, recursive wide = true ∧ compare wide value = true
    · exact ⟨value, (selected_member state facts recursive compare inputs available value).mpr ⟨member, retained⟩, accepted⟩
    · have covered : ∃ wide ∈ inputs, recursive wide = true ∧ compare wide value = true := by
        exact Classical.byContradiction (fun missing => retained (Or.inr missing))
      obtain ⟨wide, included, recursiveWide, success⟩ := covered
      exact ⟨wide, (selected_member state facts recursive compare inputs available wide).mpr ⟨included, Or.inl recursiveWide⟩,
        sound wide included value member success term accepted⟩

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- The concrete source comparison includes the free-variable gate before subsumption. -/
def compare [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs inputs : List (Value Symbol Guard))
    (meaning : Guard → Term Symbol → Bool) (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (fuel : Nat) (wide narrow : Value Symbol Guard) : Bool :=
  narrow.free.isEmpty && MergedComparisonSource.check (rows state inputs outputs meaning)
    (fun value => value.referenceOf == .empty) unconstrained fuel [] wide narrow

/-- The actual physical checker proves the selected column equation without a semantic filter assumption. -/
theorem checked_selected_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (inputs : List (Value Symbol Guard)) (available : Values state inputs)
    (meaning : Guard → Term Symbol → Bool) (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true) (fuel : Nat) (term : Term Symbol) :
    (∃ value ∈ selected closedMu (compare state outputs inputs meaning unconstrained fuel) inputs,
      EpsilonUnion.Accepts (graph state meaning) value term) ↔
      ∃ value ∈ inputs, EpsilonUnion.Accepts (graph state meaning) value term := by
  apply selected_exact state context.facts meaning closedMu _ inputs available
  intro wide _ narrow member success term accepted
  exact comparison_sound state outputs context inputs available meaning unconstrained clear fuel wide narrow
    (by simp [inventory, member]) (Bool.and_eq_true_iff.mp success).2 term accepted

/-- A retained-boundary column executes the actual repaired createUnion constructor. -/
theorem checked_retained_union [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (inputs : List (Value Symbol Guard)) (available : Values state inputs)
    (meaning : Guard → Term Symbol → Bool) (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true) (fuel : Nat) :
    let retained := selected closedMu (compare state outputs inputs meaning unconstrained fuel) inputs
    let result := run (makeUnion retained) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧
      ∀ term, EpsilonUnion.Accepts (graph result.2 meaning) result.1 term ↔
        ∃ value ∈ inputs, EpsilonUnion.Accepts (graph state meaning) value term := by
  let retained := selected closedMu (compare state outputs inputs meaning unconstrained fuel) inputs
  have retainedAvailable : Values state retained := fun value member =>
    available value (selected_subset closedMu _ inputs value member)
  have built := context.makeUnion state outputs retained retainedAvailable
  refine ⟨built.1, built.2, ?_⟩
  intro term
  exact (makeUnion_actual state outputs context retained retainedAvailable meaning term).2.2.trans
    (checked_selected_exact state outputs context inputs available meaning unconstrained clear fuel term)

/-- Direct child calls are instances of the proved well-founded source call relation. -/
theorem child_step [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard) (included : child ∈ edge.children) :
    MergedMergeTermination.Step child (.node entry edges depth free) :=
  .child entry edges depth free edge child member included

/-- Actual filtering cannot invalidate the strict rank of an ordinary column call. -/
theorem selected_column_step [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (recursive : Value Symbol Guard → Bool) (compare : Value Symbol Guard → Value Symbol Guard → Bool)
    (inputs : List (Value Symbol Guard)) (available : Values state inputs)
    (children : ∀ value ∈ inputs, ∃ edge ∈ edges, value ∈ edge.children) :
    MergedMergeTermination.Step (run (ordinaryUnion (selected recursive compare inputs)) state).1 (.node entry edges depth free) := by
  apply MergedMergeTermination.Step.column entry edges depth free _
    (fun value member => children value (selected_subset recursive compare inputs value member)) state facts.coherent facts.linked
  exact fun value member => (available value (selected_subset recursive compare inputs value member)).resident

end
end MicroCFTA.MergedPhysicalGroupColumns

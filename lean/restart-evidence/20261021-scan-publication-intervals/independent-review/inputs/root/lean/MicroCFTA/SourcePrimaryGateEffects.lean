import MicroCFTA.EndpointMemoGateClasses
import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.InternedFreshOrdinaryStoredCosts
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Physical invariants through the enabled primary gate

The current gate trace retains the endpoint descendant read. That read does
not change the constructor heap. Actual stored unfolding retains semantic
readiness, costs, and physical edge annotations. Ordered scans pass those
invariants through the exact returned heaps. Inputs need not be closed.
-/
namespace MicroCFTA.SourcePrimaryGateEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open EndpointStatefulGateTrace EqualityNormalize
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationHeap (Heap)

private def Effects (property : Guard → Prop) (before after : State Symbol Guard) : Prop :=
  SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after

private def NodeEffects (property : Guard → Prop) (value : Value Symbol Guard)
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → InternedFreshOrdinaryCostHeap.Heap before → Available before value →
    Heap property before → Effects property before after

private def ChildEffects (property : Guard → Prop) (values : List (Value Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → InternedFreshOrdinaryCostHeap.Heap before → (∀ value ∈ values, Available before value) →
    Heap property before → Effects property before after

private def EdgesEffects (property : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → InternedFreshOrdinaryCostHeap.Heap before →
    (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) →
      Heap property before → Effects property before after

private theorem node_effects_aux (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (trace : NodeTrace unconstrained reaches path value before answer after) : NodeEffects property value before after := by
  induction trace using NodeTrace.rec
      (motive_2 := fun values _ _ before _ after _ => ChildEffects property values before after)
      (motive_3 := fun _ _ edges before _ after _ => EdgesEffects property edges before after) with
  | empty | reference | union | finite | endpoint | constrained | closed =>
      intro semantic costs _ fields
      exact ⟨semantic, pure_keeps _ semantic.ready, costs, fields⟩
  | branches slow trace ih =>
      intro semantic costs available fields
      exact ih semantic costs (fun value member => available.children value member) fields
  | unfold plain opened actual trace ih =>
      intro semantic costs available fields
      obtain ⟨result, middle, done, first, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      have middleCosts := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap _ _
        semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
      have middleFields := InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property _ _
        semantic.ready.semantic.1.normal.facts fields available
      obtain ⟨finalSemantic, kept, finalCosts, finalFields⟩ := ih middleSemantic
        (by simpa only [actual, Outcome.state] using middleCosts) resultAvailable
        (by simpa only [InternedFreshOrdinaryConstraintHeap.Heap, Heap, actual, Outcome.state] using middleFields)
      exact ⟨finalSemantic, first.trans kept, finalCosts, finalFields⟩
  | missing =>
      intro semantic costs _ fields
      exact ⟨semantic, pure_keeps _ semantic.ready, costs, fields⟩
  | present found trace ih =>
      intro semantic costs available fields
      exact ih semantic costs (available _ (List.mem_of_getElem? found)) fields
  | nil =>
      intro semantic costs _ fields
      exact ⟨semantic, pure_keeps _ semantic.ready, costs, fields⟩
  | stop head ih =>
      intro semantic costs available fields
      exact ih semantic costs (fun value member => available value (by simp [member])) fields
  | next head tail headIH tailIH =>
      intro semantic costs available fields
      obtain ⟨middleSemantic, first, middleCosts, middleFields⟩ :=
        headIH semantic costs (fun value member => available value (by simp [member])) fields
      obtain ⟨finalSemantic, kept, finalCosts, finalFields⟩ := tailIH middleSemantic middleCosts
        (fun value member => first.available value (available value (by simp [member]))) middleFields
      exact ⟨finalSemantic, first.trans kept, finalCosts, finalFields⟩

/-- An actual enabled node gate preserves semantic readiness, costs, and physical annotations. -/
theorem node_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (trace : NodeTrace unconstrained reaches path value before answer after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (fields : Heap property before) :
    SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after :=
  node_effects_aux property unconstrained reaches trace semantic costs available fields

/-- An actual child lookup retains all input invariants at its exact returned heap. -/
theorem child_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {index : Nat} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    (trace : ChildTrace unconstrained reaches values index path before answer after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : ∀ value ∈ values, Available before value) (fields : Heap property before) :
    SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after := by
  cases trace with
  | missing => exact ⟨semantic, pure_keeps _ semantic.ready, costs, fields⟩
  | present found trace =>
      exact node_effects property unconstrained reaches trace semantic costs (available _ (List.mem_of_getElem? found)) fields

/-- Ordered enabled edge scans preserve all input invariants through their actual visited prefix. -/
theorem edges_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {index : Nat} {path : Path} {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} {answer : Bool}
    (trace : EdgesTrace unconstrained reaches index path edges before answer after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available before value) (fields : Heap property before) :
    SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after := by
  induction edges generalizing before answer after with
  | nil => cases trace; exact ⟨semantic, pure_keeps _ semantic.ready, costs, fields⟩
  | cons edge edges ih =>
      cases trace with
      | stop head =>
          exact child_effects property unconstrained reaches head semantic costs
            (fun value member => available value (by simp [member])) fields
      | next head tail =>
          obtain ⟨middleSemantic, first, middleCosts, middleFields⟩ :=
            child_effects property unconstrained reaches head semantic costs
              (fun value member => available value (by simp [member])) fields
          obtain ⟨finalSemantic, kept, finalCosts, finalFields⟩ := ih tail middleSemantic middleCosts
            (fun value member => first.available value (available value (by simp [member]))) middleFields
          exact ⟨finalSemantic, first.trans kept, finalCosts, finalFields⟩

/-- An actual enabled forest-path gate retains the complete invariant tuple. -/
theorem path_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    (trace : PathTrace unconstrained reaches values path before answer after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : ∀ value ∈ values, Available before value) (fields : Heap property before) :
    SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after := by
  cases trace with
  | empty => exact ⟨semantic, pure_keeps _ semantic.ready, costs, fields⟩
  | child trace => exact child_effects property unconstrained reaches trace semantic costs available fields

/-- Ordered enabled class gates retain invariants through the exact visited prefix and returned heap. -/
theorem class_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
    (trace : ClassTrace unconstrained reaches values paths before answer after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : ∀ value ∈ values, Available before value) (fields : Heap property before) :
    SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after := by
  revert fields available costs semantic
  induction trace with
  | nil => intro semantic costs _ fields; exact ⟨semantic, pure_keeps _ semantic.ready, costs, fields⟩
  | stop head =>
      intro semantic costs available fields
      exact path_effects property unconstrained reaches head semantic costs available fields
  | next head tail ih =>
      intro semantic costs available fields
      obtain ⟨middleSemantic, first, middleCosts, middleFields⟩ :=
        path_effects property unconstrained reaches head semantic costs available fields
      obtain ⟨finalSemantic, kept, finalCosts, finalFields⟩ := ih middleSemantic middleCosts
        (fun value member => first.available value (available value member)) middleFields
      exact ⟨finalSemantic, first.trans kept, finalCosts, finalFields⟩

end MicroCFTA.SourcePrimaryGateEffects

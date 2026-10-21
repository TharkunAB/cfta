import MicroCFTA.SourceCurrentRequiredPublicationHistory
import MicroCFTA.SourcePrimaryGateEffects
import MicroCFTA.SourceCurrentSecondaryEffects

/-!
# Actual publication intervals through current gates

The same gate trace supplies every completed stored unfold.
Ordered traces compose those intervals at their exact returned heaps.
Both Boolean results retain the actual reached prefix.
-/
namespace MicroCFTA.SourceCurrentGatePublicationHistory
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentNativeMuPublication (History)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private def NodePost (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Nonempty (History before after)
private def ChildPost (values : List (Value Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → InternedNestedProvenance.Values before values → Nonempty (History before after)
private def EdgesPost (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before →
    (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) → Nonempty (History before after)

namespace Primary
open EndpointStatefulGateTrace

private theorem node_history (unconstrained reaches : Value Symbol Guard → Bool)
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (actual : NodeTrace unconstrained reaches path value before answer after) : NodePost value before after := by
  induction actual using NodeTrace.rec
      (motive_2 := fun values _ _ before _ after _ => ChildPost values before after)
      (motive_3 := fun _ _ edges before _ after _ => EdgesPost edges before after) with
  | empty | reference | union | finite | endpoint | constrained | closed =>
      intro _ _ _
      exact ⟨.refl _⟩
  | branches _ _ ih =>
      intro semantic costs available
      exact ih semantic costs (fun value member => available.children value member)
  | unfold _ _ actual _ ih =>
      intro semantic costs available
      obtain ⟨result, middle, done, _, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      have middleCosts := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap _ _
        semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
      have first := SourceCurrentRequiredPublicationHistory.unfold _ _ semantic.ready available
      simp only [actual, Outcome.state] at first
      obtain ⟨first⟩ := first
      obtain ⟨last⟩ := ih middleSemantic (by simpa only [actual, Outcome.state] using middleCosts) resultAvailable
      exact ⟨.trans first last⟩
  | missing => intro _ _ _; exact ⟨.refl _⟩
  | present found _ ih =>
      intro semantic costs available
      exact ih semantic costs (available _ (List.mem_of_getElem? found))
  | nil => intro _ _ _; exact ⟨.refl _⟩
  | stop _ ih =>
      intro semantic costs available
      exact ih semantic costs (fun value member => available value (by simp [member]))
  | next head _ headIH tailIH =>
      intro semantic costs available
      have first := SourcePrimaryGateEffects.child_effects (fun _ => True) unconstrained reaches head semantic costs
        (fun value member => available value (by simp [member])) (by intro _ _ _; trivial)
      obtain ⟨headHistory⟩ := headIH semantic costs (fun value member => available value (by simp [member]))
      obtain ⟨tailHistory⟩ := tailIH first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value (by simp [member])))
      exact ⟨.trans headHistory tailHistory⟩

private theorem child_history (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {index : Nat} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ChildTrace unconstrained reaches values index path before answer after) : ChildPost values before after := by
  cases actual with
  | missing => intro _ _ _; exact ⟨.refl _⟩
  | present found actual =>
      intro semantic costs available
      exact node_history unconstrained reaches actual semantic costs (available _ (List.mem_of_getElem? found))

private theorem path_history (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : PathTrace unconstrained reaches values path before answer after) : ChildPost values before after := by
  cases actual with
  | empty => intro _ _ _; exact ⟨.refl _⟩
  | child actual => exact child_history unconstrained reaches actual

private theorem class_history (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ClassTrace unconstrained reaches values paths before answer after) : ChildPost values before after := by
  induction actual with
  | nil => intro _ _ _; exact ⟨.refl _⟩
  | stop head => exact path_history unconstrained reaches head
  | next head _ ih =>
      intro semantic costs available
      have first := SourcePrimaryGateEffects.path_effects (fun _ => True) unconstrained reaches head semantic costs available
        (by intro _ _ _; trivial)
      obtain ⟨headHistory⟩ := path_history unconstrained reaches head semantic costs available
      obtain ⟨tailHistory⟩ := ih first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value member))
      exact ⟨.trans headHistory tailHistory⟩
end Primary

/-- The same actual primary class trace supplies its complete publication interval. -/
theorem primary (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before answer after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : InternedNestedProvenance.Values before values) : Nonempty (History before after) :=
  Primary.class_history unconstrained reaches actual semantic costs available

namespace Secondary
open SourceCurrentSecondaryTrace

private theorem node_history (unconstrained : Value Symbol Guard → Bool)
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (actual : NodeTrace unconstrained path value before answer after) : NodePost value before after := by
  induction actual using NodeTrace.rec
      (motive_2 := fun values _ _ before _ after _ => ChildPost values before after)
      (motive_3 := fun _ _ edges before _ after _ => EdgesPost edges before after) with
  | empty | reference | union | finite | endpoint | constrained | closed =>
      intro _ _ _
      exact ⟨.refl _⟩
  | branches _ _ ih =>
      intro semantic costs available
      exact ih semantic costs (fun value member => available.children value member)
  | unfold _ _ actual _ ih =>
      intro semantic costs available
      obtain ⟨result, middle, done, _, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      have middleCosts := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap _ _
        semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
      have first := SourceCurrentRequiredPublicationHistory.unfold _ _ semantic.ready available
      simp only [actual, Outcome.state] at first
      obtain ⟨first⟩ := first
      obtain ⟨last⟩ := ih middleSemantic (by simpa only [actual, Outcome.state] using middleCosts) resultAvailable
      exact ⟨.trans first last⟩
  | missing => intro _ _ _; exact ⟨.refl _⟩
  | present found _ ih =>
      intro semantic costs available
      exact ih semantic costs (available _ (List.mem_of_getElem? found))
  | nil => intro _ _ _; exact ⟨.refl _⟩
  | stop _ ih =>
      intro semantic costs available
      exact ih semantic costs (fun value member => available value (by simp [member]))
  | next head _ headIH tailIH =>
      intro semantic costs available
      have first := SourceCurrentSecondaryEffects.child_effects (fun _ => True) unconstrained head semantic costs
        (fun value member => available value (by simp [member])) (by intro _ _ _; trivial)
      obtain ⟨headHistory⟩ := headIH semantic costs (fun value member => available value (by simp [member]))
      obtain ⟨tailHistory⟩ := tailIH first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value (by simp [member])))
      exact ⟨.trans headHistory tailHistory⟩

private theorem child_history (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {index : Nat} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ChildTrace unconstrained values index path before answer after) : ChildPost values before after := by
  cases actual with
  | missing => intro _ _ _; exact ⟨.refl _⟩
  | present found actual =>
      intro semantic costs available
      exact node_history unconstrained actual semantic costs (available _ (List.mem_of_getElem? found))

private theorem path_history (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : PathTrace unconstrained values path before answer after) : ChildPost values before after := by
  cases actual with
  | empty => intro _ _ _; exact ⟨.refl _⟩
  | child actual => exact child_history unconstrained actual

private theorem class_history (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ClassTrace unconstrained values paths before answer after) : ChildPost values before after := by
  induction actual with
  | nil => intro _ _ _; exact ⟨.refl _⟩
  | stop head => exact path_history unconstrained head
  | next head _ ih =>
      intro semantic costs available
      have first := SourceCurrentSecondaryEffects.path_effects (fun _ => True) unconstrained head semantic costs available
        (by intro _ _ _; trivial)
      obtain ⟨headHistory⟩ := path_history unconstrained head semantic costs available
      obtain ⟨tailHistory⟩ := ih first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value member))
      exact ⟨.trans headHistory tailHistory⟩
end Secondary

/-- The same actual secondary class trace supplies its complete publication interval. -/
theorem secondary (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before answer after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : InternedNestedProvenance.Values before values) : Nonempty (History before after) :=
  Secondary.class_history unconstrained actual semantic costs available

end MicroCFTA.SourceCurrentGatePublicationHistory

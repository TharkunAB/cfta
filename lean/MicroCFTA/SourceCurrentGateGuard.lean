import MicroCFTA.SourceCurrentConstrainedCapGuardNative
import MicroCFTA.SourcePrimaryGateEffects
import MicroCFTA.SourceCurrentSecondaryEffects

/-!
# Causal guard observations through actual current gates

An actual open Mu unfolding copies the earlier body-to-probe observations.
Ordered gate traces pass this causal heap through the exact returned states.
This invariant differs from an annotation predicate on each stored row.
-/
namespace MicroCFTA.SourceCurrentGateGuard
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConstrainedCapGuardHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem unfold_heap (annotation : Guard → Prop) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value)
    (guards : Heap annotation before) :
    Heap annotation (InternedFreshOrdinaryStoredSubstitution.unfold value before).state := by
  cases value with
  | empty | reference | node | union => exact guards
  | mu entry body depth ordinary =>
      apply SourceCurrentConstrainedCapGuardNative.execute_heap annotation body _ before semantic.ready.semantic
        (available.children body (by simp [InternedProbeProvenance.children])) _ guards
      intro name replacement found
      dsimp only at found
      split at found
      · cases found; exact available
      · cases found

private def NodePost (annotation : Guard → Prop) (value : Value Symbol Guard)
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Heap annotation before → Heap annotation after
private def ChildPost (annotation : Guard → Prop) (values : List (Value Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → InternedNestedProvenance.Values before values → Heap annotation before → Heap annotation after
private def EdgesPost (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before →
    (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) → Heap annotation before → Heap annotation after

namespace Primary
open EndpointStatefulGateTrace

private theorem node_heap (annotation : Guard → Prop) (unconstrained reaches : Value Symbol Guard → Bool)
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (actual : NodeTrace unconstrained reaches path value before answer after) : NodePost annotation value before after := by
  induction actual using NodeTrace.rec
      (motive_2 := fun values _ _ before _ after _ => ChildPost annotation values before after)
      (motive_3 := fun _ _ edges before _ after _ => EdgesPost annotation edges before after) with
  | empty | reference | union | finite | endpoint | constrained | closed =>
      intro _ _ _ guards
      exact guards
  | branches _ _ ih =>
      intro semantic costs available guards
      exact ih semantic costs (fun value member => available.children value member) guards
  | unfold _ _ actual _ ih =>
      intro semantic costs available guards
      obtain ⟨result, middle, done, _, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      have middleCosts := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap _ _
        semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
      have middleGuards := unfold_heap annotation _ _ semantic available guards
      exact ih middleSemantic (by simpa only [actual, Outcome.state] using middleCosts) resultAvailable
        (by simpa only [actual, Outcome.state] using middleGuards)
  | missing => intro _ _ _ guards; exact guards
  | present found _ ih =>
      intro semantic costs available guards
      exact ih semantic costs (available _ (List.mem_of_getElem? found)) guards
  | nil => intro _ _ _ guards; exact guards
  | stop _ ih =>
      intro semantic costs available guards
      exact ih semantic costs (fun value member => available value (by simp [member])) guards
  | next head _ headIH tailIH =>
      intro semantic costs available guards
      have first := SourcePrimaryGateEffects.child_effects (fun _ => True) unconstrained reaches head semantic costs
        (fun value member => available value (by simp [member])) (by intro _ _ _; trivial)
      exact tailIH first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value (by simp [member])))
        (headIH semantic costs (fun value member => available value (by simp [member])) guards)

private theorem child_heap (annotation : Guard → Prop) (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {index : Nat} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ChildTrace unconstrained reaches values index path before answer after) : ChildPost annotation values before after := by
  cases actual with
  | missing => intro _ _ _ guards; exact guards
  | present found actual =>
      intro semantic costs available guards
      exact node_heap annotation unconstrained reaches actual semantic costs (available _ (List.mem_of_getElem? found)) guards

private theorem path_heap (annotation : Guard → Prop) (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : PathTrace unconstrained reaches values path before answer after) : ChildPost annotation values before after := by
  cases actual with
  | empty => intro _ _ _ guards; exact guards
  | child actual => exact child_heap annotation unconstrained reaches actual

private theorem class_heap (annotation : Guard → Prop) (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ClassTrace unconstrained reaches values paths before answer after) : ChildPost annotation values before after := by
  induction actual with
  | nil => intro _ _ _ guards; exact guards
  | stop head => exact path_heap annotation unconstrained reaches head
  | next head _ ih =>
      intro semantic costs available guards
      have first := SourcePrimaryGateEffects.path_effects (fun _ => True) unconstrained reaches head semantic costs available
        (by intro _ _ _; trivial)
      exact ih first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value member))
        (path_heap annotation unconstrained reaches head semantic costs available guards)
end Primary

/-- The actual primary class gate retains causal guard observations at its exact returned heap. -/
theorem primary (annotation : Guard → Prop) (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before answer after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : InternedNestedProvenance.Values before values) (guards : Heap annotation before) : Heap annotation after :=
  Primary.class_heap annotation unconstrained reaches actual semantic costs available guards

namespace Secondary
open SourceCurrentSecondaryTrace

private theorem node_heap (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (actual : NodeTrace unconstrained path value before answer after) : NodePost annotation value before after := by
  induction actual using NodeTrace.rec
      (motive_2 := fun values _ _ before _ after _ => ChildPost annotation values before after)
      (motive_3 := fun _ _ edges before _ after _ => EdgesPost annotation edges before after) with
  | empty | reference | union | finite | endpoint | constrained | closed =>
      intro _ _ _ guards
      exact guards
  | branches _ _ ih =>
      intro semantic costs available guards
      exact ih semantic costs (fun value member => available.children value member) guards
  | unfold _ _ actual _ ih =>
      intro semantic costs available guards
      obtain ⟨result, middle, done, _, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      have middleCosts := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap _ _
        semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
      have middleGuards := unfold_heap annotation _ _ semantic available guards
      exact ih middleSemantic (by simpa only [actual, Outcome.state] using middleCosts) resultAvailable
        (by simpa only [actual, Outcome.state] using middleGuards)
  | missing => intro _ _ _ guards; exact guards
  | present found _ ih =>
      intro semantic costs available guards
      exact ih semantic costs (available _ (List.mem_of_getElem? found)) guards
  | nil => intro _ _ _ guards; exact guards
  | stop _ ih =>
      intro semantic costs available guards
      exact ih semantic costs (fun value member => available value (by simp [member])) guards
  | next head _ headIH tailIH =>
      intro semantic costs available guards
      have first := SourceCurrentSecondaryEffects.child_effects (fun _ => True) unconstrained head semantic costs
        (fun value member => available value (by simp [member])) (by intro _ _ _; trivial)
      exact tailIH first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value (by simp [member])))
        (headIH semantic costs (fun value member => available value (by simp [member])) guards)

private theorem child_heap (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {index : Nat} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ChildTrace unconstrained values index path before answer after) : ChildPost annotation values before after := by
  cases actual with
  | missing => intro _ _ _ guards; exact guards
  | present found actual =>
      intro semantic costs available guards
      exact node_heap annotation unconstrained actual semantic costs (available _ (List.mem_of_getElem? found)) guards

private theorem path_heap (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : PathTrace unconstrained values path before answer after) : ChildPost annotation values before after := by
  cases actual with
  | empty => intro _ _ _ guards; exact guards
  | child actual => exact child_heap annotation unconstrained actual

private theorem class_heap (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : ClassTrace unconstrained values paths before answer after) : ChildPost annotation values before after := by
  induction actual with
  | nil => intro _ _ _ guards; exact guards
  | stop head => exact path_heap annotation unconstrained head
  | next head _ ih =>
      intro semantic costs available guards
      have first := SourceCurrentSecondaryEffects.path_effects (fun _ => True) unconstrained head semantic costs available
        (by intro _ _ _; trivial)
      exact ih first.1 first.2.2.1
        (fun value member => first.2.1.available value (available value member))
        (path_heap annotation unconstrained head semantic costs available guards)
end Secondary

/-- The actual secondary class gate retains causal guard observations at its exact returned heap. -/
theorem secondary (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard} {answer : Bool}
    (actual : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before answer after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : InternedNestedProvenance.Values before values) (guards : Heap annotation before) : Heap annotation after :=
  Secondary.class_heap annotation unconstrained actual semantic costs available guards

end MicroCFTA.SourceCurrentGateGuard

import MicroCFTA.EnumerationPendingFragmentExpandedAvoidance

namespace MicroCFTA.EnumerationDependencies
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
variable {Symbol Guard : Type}
set_option autoImplicit false

/-- Protect old expanded classes and separate every newly stored fragment from them. -/
def ExpandedBirthHistory (before after : State Symbol Guard) : Prop :=
  (∀ slot fragment, before.values[slot]? = some (.enumerated fragment) →
    EnumerationDriver.Protected slot before after) ∧
  ∀ slot fragment, after.values[slot]? = some (.enumerated fragment) →
    before.values[slot]? = some (.enumerated fragment) ∨
      ∀ old oldFragment, before.values[old]? = some (.enumerated oldFragment) →
        FragmentAvoid after.representatives old fragment

/-- A safe state retains its old expanded classes. -/
theorem ExpandedBirthHistory.refl
    (state : State Symbol Guard) (safe : Safe state) :
    ExpandedBirthHistory state state := by
  refine ⟨?_, ?_⟩
  · intro slot fragment stored
    exact EnumerationDriver.Protected.refl slot state (enumerated_root state safe slot fragment stored).2
  · intro slot fragment stored
    exact Or.inl stored

/-- Consecutive receipts retain the same old classes and avoidance. -/
theorem ExpandedBirthHistory.trans
    (before middle after : State Symbol Guard)
    (first : ExpandedBirthHistory before middle)
    (second : ExpandedBirthHistory middle after) :
    ExpandedBirthHistory before after := by
  refine ⟨?_, ?_⟩
  · intro slot fragment stored
    have retained := first.1 slot fragment stored
    exact retained.trans (second.1 slot fragment (retained.value.trans stored))
  · intro slot fragment stored
    rcases second.2 slot fragment stored with middleStored | secondSeparate
    · rcases first.2 slot fragment middleStored with original | firstSeparate
      · exact Or.inl original
      · apply Or.inr
        intro old oldFragment oldStored
        have middleOld := (first.1 old oldFragment oldStored).value.trans oldStored
        have retained := second.1 old oldFragment middleOld
        intro uv hole related
        exact firstSeparate old oldFragment oldStored uv hole ((retained.classes uv).mp related)
    · apply Or.inr
      intro old oldFragment oldStored
      exact secondSeparate old oldFragment ((first.1 old oldFragment oldStored).value.trans oldStored)

/-- A traversal with no new expanded slots has no new dependency on old classes. -/
theorem ExpandedBirthHistory.of_origin
    (before after : State Symbol Guard) (origin : EnumeratedOrigin before after)
    (protects : ∀ slot fragment, before.values[slot]? = some (.enumerated fragment) →
      EnumerationDriver.Protected slot before after) :
    ExpandedBirthHistory before after := by
  exact ⟨protects, fun slot fragment stored => Or.inl (origin slot fragment stored)⟩

/-- One pending target write retains every old expanded class. -/
theorem ExpandedBirthHistory.write
    (before : State Symbol Guard) (target : Nat) (fragment : Fragment Symbol)
    (node : Option Nat) (bucket : List Suspended) (safe : Safe before)
    (storedTarget : before.values[target]? = some (.unenumerated node bucket))
    (pending : PendingFragment before fragment) :
    ExpandedBirthHistory before {before with values := before.values.set target (.enumerated fragment)} := by
  let after : State Symbol Guard := {before with values := before.values.set target (.enumerated fragment)}
  change ExpandedBirthHistory before after
  have oldProtection : ∀ slot old, before.values[slot]? = some (.enumerated old) →
      EnumerationDriver.Protected slot before after := by
    intro slot old stored
    have different : target ≠ slot := by
      intro same
      subst slot
      cases Option.some.inj (storedTarget.symm.trans stored)
    refine ⟨?_, (enumerated_root before safe slot old stored).2, fun _ => Iff.rfl⟩
    simp only [after, List.getElem?_set_ne different]
  refine ⟨oldProtection, ?_⟩
  intro slot produced stored
  by_cases written : slot = target
  · subst slot
    have inside : target < before.values.length :=
      (List.getElem?_eq_some_iff.mp storedTarget).1
    have fragmentSame : fragment = produced := by
      have payloadSame := stored
      simp only [after, List.getElem?_set_self inside] at payloadSame
      exact UVarValue.enumerated.inj (Option.some.inj payloadSame)
    subst produced
    apply Or.inr
    intro old oldFragment oldStored
    exact pendingFragment_avoids_protected_expanded before before fragment oldFragment old
      pending oldStored
      (EnumerationDriver.Protected.refl old before
        (enumerated_root before safe old oldFragment oldStored).2)
  · apply Or.inl
    simpa only [after, List.getElem?_set_ne (Ne.symm written)] using stored

end MicroCFTA.EnumerationDependencies

#check @MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.refl
#print axioms MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.refl
#check @MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.trans
#print axioms MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.trans
#check @MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.of_origin
#print axioms MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.of_origin
#check @MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.write
#print axioms MicroCFTA.EnumerationDependencies.ExpandedBirthHistory.write

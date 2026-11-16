import MicroCFTA.SourcePruningEnumerationIsolatedPending

namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationSchedule EnumerationDependencies EnumerationDriver EnumerationCompressionFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}
set_option autoImplicit false

/-- Old expanded slots remain protected. New expanded fragments avoid the held class. -/
structure HeldFragmentHistory (held handle : Nat) (before after : State Symbol Guard) : Prop where
  isolated : IsolatedPending held handle after
  protectedHeld : Protected held before after
  expanded : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
    before.values[slot]? = some (.enumerated fragment) → Protected slot before after
  origin : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
    after.values[slot]? = some (.enumerated fragment) →
      before.values[slot]? = some (.enumerated fragment) ∨
        FragmentAvoid after.representatives held fragment

/-- An unchanged safe core retains its isolated slot and every old expanded value. -/
theorem HeldFragmentHistory.refl
    (held handle : Nat) (state : State Symbol Guard) (safe : Safe state)
    (isolated : IsolatedPending held handle state) :
    HeldFragmentHistory held handle state state := by
  refine ⟨isolated, Protected.refl held state isolated.root, ?_, ?_⟩
  · intro slot fragment stored
    exact Protected.refl slot state (enumerated_root state safe slot fragment stored).2
  · intro slot fragment stored
    exact Or.inl stored

/-- Consecutive receipts retain old expanded values and transport new-fragment avoidance. -/
theorem HeldFragmentHistory.trans
    (held handle : Nat) (before middle after : State Symbol Guard)
    (first : HeldFragmentHistory held handle before middle)
    (second : HeldFragmentHistory held handle middle after) :
    HeldFragmentHistory held handle before after := by
  refine ⟨second.isolated, first.protectedHeld.trans second.protectedHeld, ?_, ?_⟩
  · intro slot fragment stored
    have middleStored : middle.values[slot]? = some (.enumerated fragment) :=
      (first.expanded slot fragment stored).value.trans stored
    exact (first.expanded slot fragment stored).trans (second.expanded slot fragment middleStored)
  · intro slot fragment stored
    rcases second.origin slot fragment stored with middleStored | separate
    · rcases first.origin slot fragment middleStored with originalStored | middleSeparate
      · exact Or.inl originalStored
      · exact Or.inr ((fragmentAvoid_classes middle.representatives after.representatives
          held fragment second.protectedHeld.classes).mpr middleSeparate)
    · exact Or.inr separate

/-- A complete compression frame retains the concrete fragment-history receipt. -/
theorem HeldFragmentHistory.of_frame
    (held handle : Nat) (before after : State Symbol Guard) (safe : Safe before)
    (isolated : IsolatedPending held handle before) (frame : Frame before after) :
    HeldFragmentHistory held handle before after := by
  have protects : ∀ slot, IsRoot before.representatives slot → Protected slot before after := by
    intro slot root
    refine ⟨congrArg (fun values => values[slot]?) frame.values, ?_, ?_⟩
    · obtain ⟨size, path⟩ := root
      exact ⟨size, (frame.reaches slot slot size).mpr path⟩
    · intro other
      exact SourcePruningEnumerationNativeLanguage.frame_sameClass before after frame slot other
  refine ⟨isolated.through_frame frame, protects held isolated.root, ?_, ?_⟩
  · intro slot fragment stored
    exact protects slot (enumerated_root before safe slot fragment stored).2
  · intro slot fragment stored
    rw [frame.values] at stored
    exact Or.inl stored

end MicroCFTA.EnumerationDischargeHistory

#check MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory
#check MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.refl
#check MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.trans
#check MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.of_frame
#print axioms MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.refl
#print axioms MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.trans
#print axioms MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.of_frame

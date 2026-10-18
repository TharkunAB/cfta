import MicroCFTA.SourceCurrentScopedDeletionInputs
import MicroCFTA.SourceCurrentScopedProfileInputs
import MicroCFTA.SourceCurrentStoredRootDeletionConstruction
import MicroCFTA.SourceCurrentPublicationHeapInduction
import MicroCFTA.SourceCurrentNativeMuPublication

/-!
# Source root comparison at one actual later reader

The two source calls retain their actual entry contexts and return heaps.
The common reader supplies its old payload contract and actual history.
Input profiles and original root cuts agree only on live source support.
This module proves the empty and variable cases of the stated source law.
-/
namespace MicroCFTA.SourceCurrentCausalSourceRootLaw
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Aliases)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentStoredMuProfileContract (Correct)

/-- Actual historical calls agree after live profile assignment and original root deletion. -/
def Law [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) : Prop :=
  ∀ {Atom : Type} (reader : State Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstAssignment secondAssignment : Reference → Profile) (firstCuts secondCuts : Reference → Bool)
    (firstBefore firstAfter secondBefore secondAfter : State Symbol Guard)
    (first second : Value Symbol Guard),
    Context firstBefore (inputs.map (input firstNames)) →
    Context secondBefore (inputs.map (input secondNames)) →
    Aliases expression inputs firstNames secondNames →
    SourceCurrentScopedProfileInputs.Compatible expression inputs firstNames secondNames firstAssignment secondAssignment →
    SourceCurrentScopedDeletionInputs.Compatible expression inputs firstNames secondNames firstCuts secondCuts →
    build expression (inputs.map (input firstNames)) firstBefore = .done first firstAfter →
    build expression (inputs.map (input secondNames)) secondBefore = .done second secondAfter →
    Grows firstAfter reader → Grows secondAfter reader →
    SourceCurrentPublicationHeapInduction.Heap Correct reader →
    SourceCurrentNativeMuPublication.History empty reader →
    Equivalent (deleted firstCuts first firstAssignment) (deleted secondCuts second secondAssignment)

/-- Empty source calls have equal deletion observations under arbitrary assignments. -/
theorem empty [DecidableEq (EdgeKey Symbol Guard)] : Law (.empty : Syntax Symbol Guard) := by
  intro Atom reader inputs firstNames secondNames firstAssignment secondAssignment firstCuts secondCuts
    firstBefore firstAfter secondBefore secondAfter first second
    _firstContext _secondContext _aliases _profiles _cuts firstDone secondDone
    _firstGrowth _secondGrowth _heap _history
  simp only [build,Outcome.done.injEq] at firstDone secondDone
  obtain ⟨rfl,rfl⟩ := firstDone
  obtain ⟨rfl,rfl⟩ := secondDone
  exact InternedProfileEquivalence.refl _

/-- A variable uses only the assigned profiles and cuts of its selected live input. -/
theorem variable [DecidableEq (EdgeKey Symbol Guard)] (index : Nat) : Law (.var index : Syntax Symbol Guard) := by
  intro Atom reader inputs firstNames secondNames firstAssignment secondAssignment firstCuts secondCuts
    firstBefore firstAfter secondBefore secondAfter first second
    firstContext _secondContext _aliases profiles cuts firstDone secondDone
    _firstGrowth _secondGrowth _heap _history
  simp only [build,Outcome.done.injEq] at firstDone secondDone
  obtain ⟨rfl,rfl⟩ := firstDone
  obtain ⟨rfl,rfl⟩ := secondDone
  cases found : inputs[index]? with
  | none =>
      simp only [List.getElem?_map,found,Option.map_none,Option.getD_none]
      exact InternedProfileEquivalence.refl _
  | some selected =>
      have profileAgree := SourceCurrentScopedProfileInputs.variable_input index inputs firstNames secondNames
        firstAssignment secondAssignment profiles selected found
      have cutAgree := SourceCurrentScopedDeletionInputs.variable_input index inputs firstNames secondNames
        firstCuts secondCuts cuts selected found
      simp only [List.getElem?_map,found,Option.map_some,Option.getD_some]
      cases selected with
      | inl value =>
          simp only [input]
          have available := firstContext.base.inputs value
            (List.mem_map.mpr ⟨.inl value,List.mem_of_getElem? found,rfl⟩)
          rw [SourceCurrentStoredRootDeletion.congr value firstBefore firstContext.base.normal.facts.coherent
            available firstCuts secondCuts firstAssignment secondAssignment cutAgree profileAgree]
          exact InternedProfileEquivalence.refl _
      | inr atom =>
          simp only [input,deleted]
          change firstCuts (firstNames atom) = secondCuts (secondNames atom) at cutAgree
          change firstAssignment (firstNames atom) = secondAssignment (secondNames atom) at profileAgree
          rw [cutAgree,profileAgree]
          exact InternedProfileEquivalence.refl _

end MicroCFTA.SourceCurrentCausalSourceRootLaw

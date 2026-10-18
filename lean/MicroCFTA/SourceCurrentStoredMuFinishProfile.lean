import MicroCFTA.SourceCurrentStoredMuProfileReduction
import MicroCFTA.SourceCurrentStoredMuUnusedProfile
import MicroCFTA.SourceCurrentNativeNormalizedComparison

/-!
# All stored Mu finish branches in pure reference profiles

The probe-decoded local-use test selects the actual finish branch.
A retained closed Mu stays opaque. A retained open Mu removes one finite
fresh marker. An unused smart Mu assigns Empty to its ordinary local.
The body/probe contract remains explicit for each selected payload.
-/
namespace MicroCFTA.SourceCurrentStoredMuFinishProfile
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedConstruction (finish)
open InternedRootProfile (Profile profile Equivalent)
open InternedStoredSubstitution (leaves)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryDepthHeap (usesLocal)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (Correct shadow)
open SourceCurrentStoredMuTrackedProfile (erase)

/-- The exact raw or smart return reduces to its ordinary probe in every finish branch. -/
theorem finish_profile (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (depthCorrect : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary)
    (correct : Correct entry body depth ordinary) (marker : Reference)
    (fresh : ∀ leaf ∈ leaves body, marker ∉ (match leaf with
      | .reference name => assignment name | _ => profile leaf).getD []) :
    Equivalent (denote (finish smart (.mu entry body depth ordinary)) assignment)
      (if !smart || usesLocal depth ordinary then
        if (Value.mu entry body depth ordinary).free.isEmpty then none
        else erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))
      else denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := by
  have retained (same : finish smart (.mu entry body depth ordinary) = .mu entry body depth ordinary) :
      Equivalent (denote (finish smart (.mu entry body depth ordinary)) assignment)
        (if (Value.mu entry body depth ordinary).free.isEmpty then none
          else erase marker (denote ordinary
            (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))) := by
    rw [same]
    split
    · rename_i closed
      have literal := SourceCurrentStoredProfileFunction.closed (.mu entry body depth ordinary) assignment
        (List.isEmpty_iff.mp closed)
      rw [literal]
      simpa only [profile] using (InternedProfileEquivalence.refl (none : Profile))
    · rename_i opened
      have opened : (Value.mu entry body depth ordinary).free.isEmpty = false := by
        cases found : (Value.mu entry body depth ordinary).free.isEmpty <;> simp_all
      exact SourceCurrentStoredMuProfileReduction.open_correct entry body depth ordinary assignment state coherent
        available correct opened marker fresh
  cases smart with
  | false =>
      simp only [Bool.not_false,Bool.true_or,ite_true]
      exact retained rfl
  | true =>
      cases used : usesLocal depth ordinary with
      | false =>
          simp only [Bool.not_true,Bool.false_or,Bool.false_eq_true,ite_false]
          exact SourceCurrentStoredMuUnusedProfile.smart_unused entry body depth ordinary state coherent available
            depthCorrect correct used assignment
      | true =>
          simp only [Bool.not_true,Bool.false_or,ite_true]
          exact retained (SourceCurrentNativeNormalizedComparison.retained_of_used entry body depth ordinary depthCorrect used)

/-- Finite original input profiles supply the marker for the complete finish formula. -/
theorem complete (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (depthCorrect : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary)
    (correct : Correct entry body depth ordinary) :
    ∃ marker : Reference,
      (∀ leaf ∈ leaves body, marker ∉ (match leaf with
        | .reference name => assignment name | _ => profile leaf).getD []) ∧
      Equivalent (denote (finish smart (.mu entry body depth ordinary)) assignment)
        (if !smart || usesLocal depth ordinary then
          if (Value.mu entry body depth ordinary).free.isEmpty then none
          else erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))
        else denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := by
  obtain ⟨marker,fresh⟩ := SourceCurrentStoredMuProfileReduction.fresh_marker
    ((leaves body).map (fun leaf => match leaf with | .reference name => assignment name | _ => profile leaf))
  have inputs : ∀ leaf ∈ leaves body, marker ∉ (match leaf with
      | .reference name => assignment name | _ => profile leaf).getD [] :=
    fun leaf member => fresh _ (List.mem_map.mpr ⟨leaf,member,rfl⟩)
  exact ⟨marker,inputs,finish_profile smart entry body depth ordinary assignment state coherent available
    depthCorrect correct marker inputs⟩

end MicroCFTA.SourceCurrentStoredMuFinishProfile

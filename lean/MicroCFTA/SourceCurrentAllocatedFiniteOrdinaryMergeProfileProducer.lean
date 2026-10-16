import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody

/-!
# Profiles from actual recursive merge calls

The proof follows the actual mutually recursive Run and Call graph.
Each miss derives its candidate certificate from its smaller body graph.
Completion then retains and reads the actual first winner.
No request needs a finite-ordinary premise before it runs.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open MergedOrdinaryHeight (height)
namespace Physical
export SourceCurrentMemoMergeEffects (Stored Effect effect_refl Contract)
end Physical
namespace Profiles
export SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache (Stored Certificate)
end Profiles
namespace ProfileCode
export SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode (Contract Certified)
end ProfileCode
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Every actual instruction retains both tables and discharges its local certificate. -/
theorem run_profile [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before →
      Physical.Stored before memo → Profiles.Stored memo → ProfileCode.Certified clear code before post →
      Physical.Effect before after ∧ Physical.Stored after saved ∧ Profiles.Stored saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → Physical.Stored before memo → Profiles.Stored memo →
        Available before input → Physical.Effect before after ∧ Physical.Stored after saved ∧
          Profiles.Stored saved ∧ ProfileCode.Contract input before output after) with
  | pure value state memo =>
      intro post semantic costs physical profiles checked
      exact ⟨Physical.effect_refl _ semantic costs, physical, profiles, checked⟩
  | work job state memo =>
      intro post semantic costs physical profiles checked
      exact ⟨checked.1, physical.grows checked.1.keeps, profiles, checked.2⟩
  | select fuel done =>
      intro post semantic costs physical profiles checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Physical.Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, physical.grows effect.keeps, profiles, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs physical profiles checked
      obtain ⟨effect, physicalAfter, profilesAfter, returned⟩ := ih semantic costs physical profiles checked.1
      exact ⟨effect, physicalAfter, profilesAfter, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs physical profiles checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstPhysical, firstProfiles, valid⟩ :=
        ihFirst intermediate semantic costs physical profiles firstChecked
      obtain ⟨laterEffect, laterPhysical, laterProfiles, returned⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstPhysical firstProfiles
          (nextChecked _ _ firstEffect valid)
      exact ⟨firstEffect.trans laterEffect, laterPhysical, laterProfiles, returned⟩
  | hit found =>
      rename_i semantic costs physical profiles available
      obtain ⟨_, result, closed⟩ := SourceCurrentMemoMergeEffects.hit_original semantic available physical found
      have certificate :=
        (SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.hit_certificate semantic available physical profiles found).2
      exact ⟨Physical.effect_refl _ semantic costs, physical, profiles, ⟨result, closed⟩, certificate⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs physical profiles available
      have body := SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode.lift_certified clear
        (SourceCurrentMemoMergeGraph.body top input) before _
        (SourceCurrentMemoMergeEffects.body_certified clear top input before semantic costs available)
      obtain ⟨effect, physicalAfter, profilesAfter, candidatePhysical⟩ :=
        ih _ semantic costs physical profiles body
      have candidateCertificate : Profiles.Certificate input candidate := by
        intro rows arity bound profile bounded
        have bodyProfile := SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody.body_certified
          clear top input before semantic costs available rows arity profile
        obtain ⟨_, _, _, resultProfile, resultHeight⟩ :=
          ih _ semantic costs physical profiles bodyProfile
        exact ⟨NodeShape.mono _ resultProfile
          (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.envelope_height_mono rows bounded)
          (Nat.le_refl _), resultHeight⟩
      have inputAvailable := effect.keeps.available input available
      have completed := SourceCurrentMemoMergeEffects.stored_remember physicalAfter input candidate
        inputAvailable candidatePhysical.1 candidatePhysical.2
      have winner := SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.winner_certificate
        effect.semantic inputAvailable physicalAfter profilesAfter candidateCertificate
      obtain ⟨_, result, closed⟩ := SourceCurrentMemoMergeEffects.hit_original
        effect.semantic inputAvailable completed (winner_found current input candidate)
      exact ⟨effect, completed, winner.2.2, ⟨result, closed⟩, winner.2.1⟩

/-- A completed call derives the universal output certificate for its actual memo winner. -/
theorem call_profile [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (physical : Physical.Stored before memo) (profiles : Profiles.Stored memo)
    (available : Available before input) :
    Physical.Effect before after ∧ Physical.Stored after saved ∧ Profiles.Stored saved ∧
      ProfileCode.Contract input before output after :=
  run_profile (.request actual) (fun after output => ProfileCode.Contract input before output after)
    semantic costs physical profiles ⟨available, fun _ _ _ returned => returned⟩

/-- A cold completed table derives both returned invariants without supplied certificates. -/
theorem cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    Physical.Effect before after ∧ Physical.Stored after saved ∧ Profiles.Stored saved ∧
      ProfileCode.Contract input before output after :=
  call_profile actual semantic costs (SourceCurrentMemoMergeEffects.stored_empty before)
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.empty_stored available

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer

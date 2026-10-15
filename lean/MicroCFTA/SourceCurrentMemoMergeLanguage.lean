import MicroCFTA.SourceCurrentMemoMergeLanguageCertified
import MicroCFTA.SourceCurrentMemoMergeOrigins

/-!
# Independent language coverage of recursive memo-aware merging

Actual instruction induction discharges each recursive request contract.
A hit uses its stored original record. A miss derives candidate coverage
from its actual body. The final lookup supplies the retained first winner.
No theorem equates this execution with an uncached body replay.
-/
namespace MicroCFTA.SourceCurrentMemoMergeLanguage
open Cache Language InternedConstructorTemplates InternedGuardedLanguage InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual recursive instructions derive coverage and retain all completed cache answers. -/
theorem run_language
    (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    {code : Code Symbol Guard Output} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before →
      Stored before memo → CacheCovers holds ambient memo →
      Certified (Contract holds ambient) clear code before post →
      Effect before after ∧ Stored after saved ∧ CacheCovers holds ambient saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → Stored before memo → CacheCovers holds ambient memo →
          Available before input → Effect before after ∧ Stored after saved ∧ CacheCovers holds ambient saved ∧
            Contract holds ambient input before output after) with
  | pure value state memo =>
      intro post semantic costs stored covered checked
      exact ⟨effect_refl _ semantic costs, stored, covered, checked⟩
  | work job state memo =>
      intro post semantic costs stored covered checked
      exact ⟨checked.1, stored.grows checked.1.keeps, covered, checked.2⟩
  | select fuel done =>
      intro post semantic costs stored covered checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, stored.grows effect.keeps, covered, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs stored covered checked
      obtain ⟨effect, retained, finalCovered, returned⟩ := ih semantic costs stored covered checked.1
      exact ⟨effect, retained, finalCovered, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored covered checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstStored, firstCovered, valid⟩ :=
        ihFirst intermediate semantic costs stored covered firstChecked
      obtain ⟨laterEffect, laterStored, laterCovered, returned⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstStored firstCovered
          (nextChecked _ _ firstEffect valid)
      exact ⟨firstEffect.trans laterEffect, laterStored, laterCovered, returned⟩
  | hit found =>
      rename_i semantic costs stored covered available
      obtain ⟨same, result, closed⟩ := hit_original semantic available stored found
      have inclusion := covered _ _ found
      rw [same] at inclusion
      exact ⟨effect_refl _ semantic costs, stored, covered, ⟨result, closed⟩, inclusion⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored covered available
      obtain ⟨effect, retained, currentCovered, physical, inclusion⟩ :=
        ih _ semantic costs stored covered
          (body_certified clear top holds ambient clearTrue topTrue input before semantic costs available)
      have inputAvailable := effect.keeps.available input available
      have completed := stored_remember retained input candidate inputAvailable physical.1 physical.2
      have finalCovered := cache_covers_remember currentCovered input candidate inclusion
      obtain ⟨same, winnerAvailable, winnerClosed⟩ :=
        hit_original effect.semantic inputAvailable completed (winner_found current input candidate)
      have winnerCovers := finalCovered _ _ (winner_found current input candidate)
      rw [same] at winnerCovers
      exact ⟨effect, completed, finalCovered, ⟨winnerAvailable, winnerClosed⟩, winnerCovers⟩

/-- Completed requests retain every accepted input term through literal hits and recursive misses. -/
theorem call_language
    (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    {input output : Value Symbol Guard} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (stored : Stored before memo) (covered : CacheCovers holds ambient memo)
    (available : Available before input) :
    Effect before after ∧ Stored after saved ∧ CacheCovers holds ambient saved ∧
      Contract holds ambient input before output after :=
  run_language clear top holds ambient clearTrue topTrue (.request actual)
    (fun after output => Contract holds ambient input before output after)
    semantic costs stored covered ⟨available, fun _ _ _ returned => returned⟩

/-- An empty result cache derives physical and semantic validity without a stored-answer premise. -/
theorem cold_language
    (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    {input output : Value Symbol Guard} {before after : State Symbol Guard}
    {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    Effect before after ∧ Stored after saved ∧ CacheCovers holds ambient saved ∧
      Contract holds ambient input before output after :=
  call_language clear top holds ambient clearTrue topTrue actual semantic costs
    (stored_empty before) (cache_covers_empty holds ambient) available

end MicroCFTA.SourceCurrentMemoMergeLanguage

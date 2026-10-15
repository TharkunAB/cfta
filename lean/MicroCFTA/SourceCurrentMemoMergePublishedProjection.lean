import MicroCFTA.SourceCurrentMemoMergePublishedState

/-!
# Completed projection of sequential published merge execution

Actual published instructions derive one completed memo-aware execution.
The proof retains the exact output, constructor heap, and completed map.
Captured-record and publication invariants follow from their initial facts.
The forcing graph supplies no result-language or future-validity premise.
-/
namespace MicroCFTA.SourceCurrentMemoMergePublishedProjection
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph (Code Memo)
open SourceCurrentMergeResultMemo (Producer Published)
open SourceCurrentMemoMergePublishedGraph (Run Call publish selected)
open SourceCurrentMemoMergePublishedState
open SourceCurrentMemoMergeEffects (Effect Stored Contract Certified)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual published instructions derive their exact completed execution and all physical state invariants. -/
theorem run_project
    {clear : Guard → Bool} {top : Guard} {active : List Producer} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {table saved : Published} {memo completed : Memo Symbol Guard} {output : Output}
    (actual : Run clear top active code before table memo output after saved completed) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Stored before memo →
      Known before table → CompletedPublished table memo → Certified Contract clear code before post →
      SourceCurrentMemoMergeGraph.Run clear top code before memo output after completed ∧
        Effect before after ∧ Stored after completed ∧ Known after saved ∧ CompletedPublished saved completed ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun active input before table memo output after saved completed _ =>
        SemanticReady before → CostHeap before → Stored before memo → Known before table → CompletedPublished table memo →
          Available before input → SourceCurrentMemoMergeGraph.Call clear top input before memo output after completed ∧
            Effect before after ∧ Stored after completed ∧ Known after saved ∧ CompletedPublished saved completed ∧
              Contract input before output after) with
  | pure active value heap table memo =>
      intro post semantic costs stored known covered checked
      exact ⟨.pure _ _ _, SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, stored, known, covered, checked⟩
  | work active job heap table memo =>
      intro post semantic costs stored known covered checked
      exact ⟨.work _ _ _, checked.1, stored.grows checked.1.keeps, known.grows checked.1.keeps, covered, checked.2⟩
  | select fuel done =>
      intro post semantic costs stored known covered checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨.select fuel done, effect, stored.grows effect.keeps, known.grows effect.keeps,
        covered, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs stored known covered checked
      obtain ⟨lower, effect, retained, finalKnown, finalCovered, result⟩ :=
        ih semantic costs stored known covered checked.1
      exact ⟨.request lower, effect, retained, finalKnown, finalCovered, checked.2 _ _ effect result⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored known covered checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨lowerFirst, firstEffect, firstStored, firstKnown, firstCovered, valid⟩ :=
        ihFirst intermediate semantic costs stored known covered firstChecked
      obtain ⟨lowerLater, laterEffect, laterStored, laterKnown, laterCovered, result⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstStored firstKnown firstCovered
          (nextChecked _ _ firstEffect valid)
      exact ⟨.bind lowerFirst lowerLater, firstEffect.trans laterEffect, laterStored, laterKnown, laterCovered, result⟩
  | hit published found =>
      rename_i semantic costs stored known covered available
      obtain ⟨_, result, closed⟩ := SourceCurrentMemoMergeEffects.hit_original semantic available stored found
      exact ⟨.hit found, SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, stored, known, covered, result, closed⟩
  | @force memo active table input before candidate after current evaluated ticket absent idle body ih =>
      rename_i semantic costs stored known covered available
      have same := selected_original (ticket := ticket) known semantic available
      have originalAvailable := selected_available known input ticket available
      obtain ⟨lower, effect, retained, finalKnown, finalCovered, physical⟩ :=
        ih _ semantic costs stored (known.publish input ticket available) (covered.publish input ticket)
          (SourceCurrentMemoMergeEffects.body_certified clear top (selected table input ticket).original before
            semantic costs originalAvailable)
      have inputAbsent : memo input.referenceOf = none := by simpa only [same] using absent
      have stillAbsent : evaluated input.referenceOf = none := by
        simpa only [same] using SourceCurrentMemoMergePublishedGraph.force_body_absent body absent
      have lowerBody : SourceCurrentMemoMergeGraph.Run clear top (SourceCurrentMemoMergeGraph.body top input)
          before memo candidate after evaluated := by simpa only [same] using lower
      have winner := (SourceCurrentMemoMergeGraph.remember_absent evaluated input candidate stillAbsent).2
      have lowerCall : SourceCurrentMemoMergeGraph.Call clear top input before memo candidate after
          (SourceCurrentMemoMergeGraph.remember evaluated (selected table input ticket).original candidate) := by
        simpa only [same, winner] using (SourceCurrentMemoMergeGraph.Call.miss inputAbsent lowerBody)
      have completedStored := SourceCurrentMemoMergeEffects.stored_remember retained _ candidate
        (effect.keeps.available _ originalAvailable) physical.1 physical.2
      have installed := body.published_extends _ _ (SourceCurrentMemoMergePublishedGraph.selected_present table input ticket)
      have present : current (selected table input ticket).original.referenceOf = some (selected table input ticket) := by
        simpa only [same] using installed
      exact ⟨lowerCall, effect, completedStored, finalKnown,
        finalCovered.remember _ candidate (selected table input ticket) present,
        by simpa only [same] using physical⟩

/-- Each completed source force has the exact memo-aware output and constructor effects of its projection. -/
theorem call_project
    {clear : Guard → Bool} {top : Guard} {active : List Producer} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {table saved : Published} {memo completed : Memo Symbol Guard}
    (actual : Call clear top active input before table memo output after saved completed)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (known : Known before table) (covered : CompletedPublished table memo) (available : Available before input) :
    SourceCurrentMemoMergeGraph.Call clear top input before memo output after completed ∧
      Effect before after ∧ Stored after completed ∧ Known after saved ∧ CompletedPublished saved completed ∧
        Contract input before output after := by
  obtain ⟨lower, checked⟩ := run_project (.request actual) (fun after output => Contract input before output after)
    semantic costs stored known covered ⟨available, fun _ _ _ returned => returned⟩
  exact ⟨SourceCurrentMemoMergeGraph.Run.request_iff.mp lower, checked⟩

end MicroCFTA.SourceCurrentMemoMergePublishedProjection

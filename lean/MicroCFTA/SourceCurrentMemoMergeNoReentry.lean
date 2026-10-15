import MicroCFTA.SourceCurrentMemoMergePublishedLift

/-!
# A well-formed merge body cannot complete its own result key

The auxiliary publication table is computed from the initial completed map.
Actual body request bounds then lift the body under its own active producer.
Active-key retention proves the original completed lookup unchanged. No
returned-key absence or candidate-winner premise is supplied.
-/
namespace MicroCFTA.SourceCurrentMemoMergeNoReentry
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph (Memo body Run Call remember)
open SourceCurrentMemoMergeEffects
open SourceCurrentMergeResultMemo (Producer Published)
open SourceCurrentMemoMergePublishedGraph (publish selected)
open SourceCurrentMemoMergePublishedState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private def fromMemo (memo : Memo Symbol Guard) : Published :=
  fun key => (memo key).map (fun entry => ⟨0, entry.original⟩)

private theorem fromMemo_known {heap : Heap} {memo : Memo Symbol Guard} (stored : Stored heap memo) :
    Known heap (fromMemo memo) := by
  constructor
  · intro key producer found
    cases prior : memo key with
    | none => simp only [fromMemo, prior, Option.map_none] at found; cases found
    | some entry =>
        have same : Producer.mk 0 entry.original = producer := Option.some.inj (by simpa only [fromMemo, prior, Option.map_some] using found)
        cases same
        exact (stored key entry prior).1
  · intro key producer found
    cases prior : memo key with
    | none => simp only [fromMemo, prior, Option.map_none] at found; cases found
    | some entry =>
        have same : Producer.mk 0 entry.original = producer := Option.some.inj (by simpa only [fromMemo, prior, Option.map_some] using found)
        cases same
        exact (stored key entry prior).2.1

private theorem fromMemo_covered (memo : Memo Symbol Guard) : CompletedPublished (fromMemo memo) memo := by
  intro key entry found
  exact ⟨⟨0, entry.original⟩, by simp only [fromMemo, found, Option.map_some]⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual well-formed source body preserves its own initial completed-key lookup. -/
theorem body_key_unchanged {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Heap} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (body top input) before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    saved input.referenceOf = memo input.referenceOf := by
  let table := fromMemo memo
  have known : Known before table := fromMemo_known stored
  have covered : CompletedPublished table memo := fromMemo_covered memo
  have original : (selected table input 0).original = input := selected_original known semantic available
  have frames : SourceCurrentMemoMergePublishedLift.Frames (MergedOrdinaryHeight.height input) before [selected table input 0] := by
    intro producer member
    cases List.mem_singleton.mp member
    exact ⟨by simpa only [original] using available, by simp only [original]; exact Nat.le_refl _⟩
  obtain ⟨final, lifted, _, _⟩ := SourceCurrentMemoMergePublishedLift.run_lift actual (MergedOrdinaryHeight.height input)
    (fun heap value => Contract input before value heap) semantic costs stored
    (SourceCurrentMemoMergeRequestBounds.body_bounded clear top input before semantic costs available)
    [selected table input 0] (publish table input 0) (known.publish input 0 available) (covered.publish input 0) frames
  simpa only [original] using lifted.active_unchanged (selected table input 0) List.mem_cons_self

/-- An initially absent result key is absent after its actual body completes. -/
theorem body_absent {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Heap} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (body top input) before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input)
    (absent : memo input.referenceOf = none) : saved input.referenceOf = none :=
  (body_key_unchanged actual semantic costs stored available).trans absent

/-- A well-formed actual miss returns its own body candidate and stores that candidate at the requested key. -/
theorem call_miss_candidate {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Heap} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (absent : memo input.referenceOf = none)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    ∃ current, Run clear top (body top input) before memo output after current ∧
      current input.referenceOf = none ∧ saved = remember current input output := by
  obtain ⟨candidate, current, bodyRun, completed, returned⟩ := actual.miss_cases absent
  have stillAbsent := body_absent bodyRun semantic costs stored available absent
  have winner := (SourceCurrentMemoMergeGraph.remember_absent current input candidate stillAbsent).2
  have same : output = candidate := by simpa only [winner] using returned
  exact ⟨current, by simpa only [same] using bodyRun, stillAbsent, by simpa only [same] using completed⟩

end MicroCFTA.SourceCurrentMemoMergeNoReentry

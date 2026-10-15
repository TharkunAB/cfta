import MicroCFTA.SourceCurrentMemoMergePublishedState
import MicroCFTA.SourceCurrentMemoMergeRequestBounds

/-!
# Sequential publication derived from completed recursive merge execution

The lifting retains the exact constructor heap and completed result table.
Each miss publishes its captured original before its actual body runs.
Ordinary height and physical identity exclude running ancestor keys.
The completed table is proof state for evaluation status. This result does
not model concurrent evaluation or literal GHC forcing.
-/
namespace MicroCFTA.SourceCurrentMemoMergePublishedLift
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph (Code Memo body)
open SourceCurrentMemoMergeEffects
open SourceCurrentMemoMergeRequestBounds (Bounded body_bounded)
open SourceCurrentMergeResultMemo (Producer Published)
open SourceCurrentMemoMergePublishedGraph (publish selected selected_present)
open SourceCurrentMemoMergePublishedState
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard
local notation "OldRun" => SourceCurrentMemoMergeGraph.Run
local notation "OldCall" => SourceCurrentMemoMergeGraph.Call
local notation "NewRun" => SourceCurrentMemoMergePublishedGraph.Run
local notation "NewCall" => SourceCurrentMemoMergePublishedGraph.Call
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Active frames retain resident originals whose heights bound the current body. -/
def Frames (limit : Nat) (heap : Heap) (active : List Producer) : Prop :=
  ∀ producer ∈ active, Available heap producer.original ∧ limit ≤ height producer.original

/-- Each requested input is strictly below every active ancestor original. -/
def Above (input : Value Symbol Guard) (heap : Heap) (active : List Producer) : Prop :=
  ∀ producer ∈ active, Available heap producer.original ∧ height input < height producer.original

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem verified {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : Heap} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : OldRun clear top code before memo output after saved)
    (limit : Nat) (post : Heap → Output → Prop) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Stored before memo) (checked : Bounded limit clear code before post) :
    Effect before after ∧ Stored after saved ∧ post after output := by
  obtain ⟨events, direct⟩ := SourceCurrentMemoMergeRequestBounds.direct_exists actual
  have checked := direct.bounded limit post semantic costs stored checked
  exact ⟨checked.1, checked.2.1, checked.2.2.1⟩

/-- Actual instruction induction inserts serial publication before every newly forced body. -/
theorem run_lift {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : Heap} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : OldRun clear top code before memo output after saved) :
    ∀ (limit : Nat) (post : Heap → Output → Prop), SemanticReady before → CostHeap before → Stored before memo →
      Bounded limit clear code before post → ∀ (active : List Producer) (table : Published),
        Known before table → CompletedPublished table memo → Frames limit before active →
        ∃ final, NewRun clear top active code before table memo output after final saved ∧
          Known after final ∧ CompletedPublished final saved := by
  induction actual using SourceCurrentMemoMergeGraph.Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → Stored before memo → Available before input →
          ∀ (active : List Producer) (table : Published), Known before table → CompletedPublished table memo → Above input before active →
            ∃ final, NewCall clear top active input before table memo output after final saved ∧
              Known after final ∧ CompletedPublished final saved) with
  | pure value heap memo =>
      intro _ _ _ _ _ _ active table known covered _
      exact ⟨table, .pure active value heap table memo, known, covered⟩
  | work job heap memo =>
      intro _ _ _ _ _ checked active table known covered _
      exact ⟨table, .work active job heap table memo, known.grows checked.1.keeps, covered⟩
  | select fuel done =>
      intro _ _ semantic costs _ checked _ table known covered _
      have effects := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _ semantic costs checked.1 _ _ done
      exact ⟨table, .select fuel done, known.grows effects.keeps, covered⟩
  | request actual ih =>
      intro limit _ semantic costs stored checked active table known covered frames
      obtain ⟨final, called, finalKnown, finalCovered⟩ := ih semantic costs stored checked.1 active table known covered (by
        intro producer member
        have frame := frames producer member
        exact ⟨frame.1, Nat.lt_of_lt_of_le checked.2.1 frame.2⟩)
      exact ⟨final, .request called, finalKnown, finalCovered⟩
  | bind first later ihFirst ihLater =>
      intro limit post semantic costs stored checked active table known covered frames
      obtain ⟨pre, firstChecked, nextChecked⟩ := checked
      obtain ⟨current, firstRun, middleKnown, middleCovered⟩ := ihFirst limit pre semantic costs stored firstChecked active table known covered frames
      obtain ⟨effect, middleStored, ready⟩ := verified first limit pre semantic costs stored firstChecked
      obtain ⟨final, laterRun, finalKnown, finalCovered⟩ := ihLater limit post effect.semantic effect.costs middleStored
        (nextChecked _ _ effect ready) active current middleKnown middleCovered (by
          intro producer member
          have frame := frames producer member
          exact ⟨effect.keeps.available producer.original frame.1, frame.2⟩)
      exact ⟨final, .bind firstRun laterRun, finalKnown, finalCovered⟩
  | hit found =>
      rename_i semantic costs stored available active table known covered above
      obtain ⟨producer, published⟩ := covered _ _ found
      exact ⟨table, .hit published found, known, covered⟩
  | @miss memo input before candidate after current absent bodyRun ih =>
      rename_i semantic costs stored available active table known covered above
      let producer := selected table input 0
      have original : (selected table input 0).original = input := selected_original (ticket := 0) known semantic available
      have prefixKnown := known.publish input 0 available
      have prefixCovered := covered.publish input 0
      have frames : Frames (height input) before (producer :: active) := by
        intro ancestor member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨by simpa only [producer, original] using available, by simp only [producer, original]; exact Nat.le_refl _⟩
        · have frame := above ancestor member
          exact ⟨frame.1, Nat.le_of_lt frame.2⟩
      obtain ⟨final, forcedBody, finalKnown, finalCovered⟩ := ih (height input) (fun heap value => Contract input before value heap)
        semantic costs stored (body_bounded _ _ input before semantic costs available)
        (producer :: active) (publish table input 0) prefixKnown prefixCovered frames
      have stillAbsent : current input.referenceOf = none := by
        have unchanged := forcedBody.active_unchanged producer List.mem_cons_self
        simpa only [producer, original] using unchanged.trans (by simpa only [producer, original] using absent)
      have winner := (SourceCurrentMemoMergeGraph.remember_absent current input candidate stillAbsent).2
      have present : final input.referenceOf = some producer :=
        forcedBody.published_extends _ _ (selected_present table input 0)
      have forced : NewCall clear top active input before table memo candidate after final
          (SourceCurrentMemoMergeGraph.remember current producer.original candidate) := by
        refine .force (evaluated := current) 0 ?_ ?_ ?_
        · simpa only [producer, original] using absent
        · intro ancestor member equal
          have frame := above ancestor member
          have same := InternedFreshProbeKeys.resident_reference_injective before semantic.ready.semantic.1.normal.facts.coherent
            ancestor.original input frame.1.resident available.resident (by simpa only [producer, original] using equal)
          have less := frame.2
          rw [same] at less
          omega
        · simpa only [producer, original] using forcedBody
      exact ⟨final, by simpa only [winner, producer, original] using forced, finalKnown,
        finalCovered.remember input candidate producer present⟩

private def RequestReceipt (clear : Guard → Bool) (top : Guard) (active : List Producer)
    (code : Code Symbol Guard Output) (before : Heap) (table : Published) (memo : Memo Symbol Guard)
    (output : Output) (after : Heap) (final : Published) (saved : Memo Symbol Guard) : Prop :=
  match code with
  | .request input => NewCall clear top active input before table memo output after final saved
  | _ => True

private theorem request_receipt {clear : Guard → Bool} {top : Guard} {active : List Producer} {code : Code Symbol Guard Output}
    {before after : Heap} {table final : Published} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : NewRun clear top active code before table memo output after final saved) :
    RequestReceipt clear top active code before table memo output after final saved := by
  induction actual using SourceCurrentMemoMergePublishedGraph.Run.rec (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True) with
  | pure | work | select | bind => trivial
  | request actual _ => exact actual
  | hit | force => trivial

/-- A completed call lifts to serial early publication from legitimate current heap and table invariants. -/
theorem call_lift {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Heap} {memo saved : Memo Symbol Guard}
    (actual : OldCall clear top input before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input)
    (active : List Producer) (table : Published) (known : Known before table) (covered : CompletedPublished table memo)
    (above : Above input before active) :
    ∃ final, NewCall clear top active input before table memo output after final saved ∧
      Known after final ∧ CompletedPublished final saved := by
  have checked : Bounded (height input + 1) clear (.request input) before (fun heap value => Contract input before value heap) :=
    ⟨available, Nat.lt_succ_self _, fun _ _ _ returned => returned⟩
  obtain ⟨final, lifted, finalKnown, finalCovered⟩ := run_lift (.request actual) (height input + 1) _ semantic costs stored checked
    active table known covered (by
      intro producer member
      have frame := above producer member
      exact ⟨frame.1, frame.2⟩)
  exact ⟨final, request_receipt lifted, finalKnown, finalCovered⟩

/-- Empty publication and evaluation tables derive a complete serial publication history for an actual cold call. -/
theorem cold_lift {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Heap} {saved : Memo Symbol Guard}
    (actual : OldCall clear top input before SourceCurrentMemoMergeGraph.empty output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    ∃ final, NewCall clear top [] input before (fun _ => none) SourceCurrentMemoMergeGraph.empty output after final saved ∧
      Known after final ∧ CompletedPublished final saved :=
  call_lift actual semantic costs (stored_empty before) available [] (fun _ => none)
    (Known.empty before) (CompletedPublished.empty _) (by simp [Above])

end MicroCFTA.SourceCurrentMemoMergePublishedLift

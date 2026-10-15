import MicroCFTA.SourceCurrentMemoMergeEffects
import MicroCFTA.SourceCurrentSubsumesQueryMemos

/-!
# Global memo receipts through completed recursive merge requests

Hits leave the heap and three global tables unchanged. Misses retain the
actual ordered recursive body reads. Selection receipts include actual
bounded row exposure and its unfolding effects.
-/
namespace MicroCFTA.SourceCurrentMemoMergeQueryMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect

mutual
  /-- Receipts retain the source instruction order and exact completed result-table states. -/
  inductive Reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
      {Output : Type} → Code Symbol Guard Output → State Symbol Guard → Memo Symbol Guard →
        Output → State Symbol Guard → Memo Symbol Guard → Memos → Memos → Prop where
    | pure (value : Output) (heap : State Symbol Guard) (memo : Memo Symbol Guard) (memos : Memos) :
        Reads clear top (.pure value) heap memo value heap memo memos memos
    | work (job : Work Symbol Guard Output) (heap : State Symbol Guard) (memo : Memo Symbol Guard) (memos : Memos) :
        Reads clear top (.work job) heap memo (run job heap).1 (run job heap).2 memo memos memos
    | select (fuel : Nat) (done : SourceMergedSelection.select clear fuel inputs before = .done values after)
        (receipt : SourceCurrentSubsumesQueryMemos.Reads (SourceMergedSelection.select clear fuel inputs) before values after memos saved) :
        Reads clear top (.select inputs) before memo values after memo memos saved
    | request (actual : CallReads clear top input before memo output after saved memos final) :
        Reads clear top (.request input) before memo output after saved memos final
    | bind (first : Reads clear top code before memo value middle current memos saved)
        (later : Reads clear top (next value) middle current output after completed saved final) :
        Reads clear top (.bind code next) before memo output after completed memos final

  /-- A completed hit has no body read; a miss carries only its actual recursive reads. -/
  inductive CallReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
      Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Memos → Memos → Prop where
    | hit (found : memo input.referenceOf = some entry) (memos : Memos) :
        CallReads clear top input before memo entry.result before memo memos memos
    | miss (absent : memo input.referenceOf = none)
        (actual : Reads clear top (body top input) before memo candidate after current memos saved) :
        CallReads clear top input before memo (winner current input candidate).result after (remember current input candidate) memos saved
end

/-- Each instruction receipt erases to the actual completed memo-aware graph. -/
theorem Reads.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output} {memos final : Memos}
    (receipt : Reads clear top code before memo output after saved memos final) :
    Run clear top code before memo output after saved := by
  induction receipt using Reads.rec
      (motive_2 := fun input before memo output after saved _ _ _ => Call clear top input before memo output after saved) with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | select fuel done _ => exact .select fuel done
  | request _ ih => exact .request ih
  | bind _ _ first later => exact .bind first later
  | hit found _ => exact .hit found
  | miss absent _ ih => exact .miss absent ih

/-- Each completed-call receipt retains its literal hit or recursive miss graph. -/
theorem CallReads.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    (receipt : CallReads clear top input before memo output after saved memos final) :
    Call clear top input before memo output after saved := by
  induction receipt using CallReads.rec
      (motive_1 := fun {_} code before memo output after saved _ _ _ => Run clear top code before memo output after saved) with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | select fuel done _ => exact .select fuel done
  | request _ ih => exact .request ih
  | bind _ _ first later => exact .bind first later
  | hit found _ => exact .hit found
  | miss absent _ ih => exact .miss absent ih

/-- Actual instruction receipts preserve both original query tables. -/
theorem Reads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output} {memos final : Memos}
    (receipt : Reads clear top code before memo output after saved memos final) : final.query = memos.query := by
  induction receipt using Reads.rec (motive_2 := fun _ _ _ _ _ _ memos final _ => final.query = memos.query) with
  | pure | work => rfl
  | select _ _ actual => exact actual.query
  | request _ ih => exact ih
  | bind _ _ first later => exact later.trans first
  | hit => rfl
  | miss _ _ ih => exact ih

/-- Completed-call receipts preserve both original query tables. -/
theorem CallReads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    (receipt : CallReads clear top input before memo output after saved memos final) : final.query = memos.query :=
  (Reads.request receipt).query

/-- A request instruction retains its complete recursive receipt. -/
def RequestReceipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (output : Output)
    (after : State Symbol Guard) (saved : Memo Symbol Guard) (memos final : Memos) : Prop :=
  match code with
  | .request input => CallReads clear top input before memo output after saved memos final
  | _ => True

theorem Reads.request_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output} {memos final : Memos}
    (receipt : Reads clear top code before memo output after saved memos final) :
    RequestReceipt clear top code before memo output after saved memos final := by
  induction receipt using Reads.rec (motive_2 := fun _ _ _ _ _ _ _ _ _ => True) with
  | pure | work | select | bind => trivial
  | request actual _ => exact actual
  | hit | miss => trivial

/-- Ordered global receipts preserve prior unfolding entries and both query tables. -/
theorem effect_trans [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {memos saved final : Memos}
    (first : GlobalEffect before middle memos saved) (later : GlobalEffect middle after saved final) :
    GlobalEffect before after memos final :=
  ⟨first.keeps.trans later.keeps, later.semantic, later.costs, later.valid,
    extends_trans first.retained later.retained, later.query.trans first.query⟩

/-- Actual instruction induction derives all three global receipts and their final validity. -/
theorem run_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Stored before memo →
      Certified Contract clear code before post → ∀ memos, Valid before memos →
        ∃ final, Reads clear top code before memo output after saved memos final ∧
          GlobalEffect before after memos final ∧ Stored after saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => SemanticReady before → CostHeap before →
        Stored before memo → Available before input → ∀ memos, Valid before memos →
          ∃ final, CallReads clear top input before memo output after saved memos final ∧
            GlobalEffect before after memos final ∧ Stored after saved ∧ Contract input before output after) with
  | pure value heap memo =>
      intro post semantic costs stored checked memos valid
      exact ⟨memos, .pure value heap memo memos,
        ⟨pure_keeps _ semantic.ready, semantic, costs, valid, extends_refl _, rfl⟩, stored, checked⟩
  | work job heap memo =>
      intro post semantic costs stored checked memos valid
      have coherent := SourceQueryUnfoldMemo.valid_grows heap (run job heap).2 semantic checked.1.keeps memos valid
      exact ⟨memos, .work job heap memo memos,
        ⟨checked.1.keeps, checked.1.semantic, checked.1.costs, coherent, extends_refl _, rfl⟩,
        stored.grows checked.1.keeps, checked.2⟩
  | select fuel done =>
      intro post semantic costs stored checked memos valid
      obtain ⟨final, receipt, effect⟩ := SourceCurrentSubsumesQueryMemos.select_memos _ fuel _ _ semantic costs
        checked.1 checked.2.1 _ _ done memos valid
      have physical : SourceCurrentMemoMergeEffects.Effect _ _ := ⟨effect.keeps, effect.semantic, effect.costs⟩
      exact ⟨final, .select fuel done receipt, effect, stored.grows effect.keeps, checked.2.2 fuel _ _ done physical⟩
  | request actual ih =>
      intro post semantic costs stored checked memos valid
      obtain ⟨final, receipt, effect, retained, returned⟩ := ih semantic costs stored checked.1 memos valid
      exact ⟨final, .request receipt, effect, retained,
        checked.2 _ _ ⟨effect.keeps, effect.semantic, effect.costs⟩ returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored checked memos valid
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨current, firstReceipt, firstEffect, firstStored, ready⟩ := ihFirst intermediate semantic costs stored firstChecked memos valid
      obtain ⟨final, laterReceipt, laterEffect, laterStored, returned⟩ := ihLater post firstEffect.semantic firstEffect.costs firstStored
        (nextChecked _ _ ⟨firstEffect.keeps, firstEffect.semantic, firstEffect.costs⟩ ready) current firstEffect.valid
      exact ⟨final, .bind firstReceipt laterReceipt, effect_trans firstEffect laterEffect, laterStored, returned⟩
  | hit found =>
      rename_i semantic costs stored available memos valid
      obtain ⟨same, result, closed⟩ := hit_original semantic available stored found
      exact ⟨memos, .hit found memos,
        ⟨pure_keeps _ semantic.ready, semantic, costs, valid, extends_refl _, rfl⟩, stored, result, closed⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored available memos valid
      obtain ⟨final, receipt, effect, retained, result, closed⟩ := ih _ semantic costs stored
        (body_certified _ _ input before semantic costs available) memos valid
      have inputAvailable := effect.keeps.available input available
      have completed := stored_remember retained input candidate inputAvailable result closed
      obtain ⟨same, winnerAvailable, winnerClosed⟩ := hit_original effect.semantic inputAvailable completed (winner_found current input candidate)
      exact ⟨final, .miss absent receipt, effect, completed, winnerAvailable, winnerClosed⟩

/-- Completed actual requests derive coherent final tables without replaying cache-hit bodies. -/
theorem call_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Stored before memo) (available : Available before input)
    (memos : Memos) (valid : Valid before memos) :
    ∃ final, CallReads clear top input before memo output after saved memos final ∧
      GlobalEffect before after memos final ∧ Stored after saved ∧ Available after output ∧ (input.free = [] → output.free = []) := by
  obtain ⟨final, receipt, effect, retained, returned⟩ := run_memos (.request actual)
    (fun after output => Contract input before output after) semantic costs stored
    ⟨available, fun _ _ _ returned => returned⟩ memos valid
  exact ⟨final, receipt.request_receipt, effect, retained, returned⟩

/-- Empty result tables need no supplied warm-cache physical invariant. -/
theorem cold_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before input) (memos : Memos) (valid : Valid before memos) :
    ∃ final, CallReads clear top input before empty output after saved memos final ∧
      GlobalEffect before after memos final ∧ Stored after saved ∧ Available after output ∧ (input.free = [] → output.free = []) :=
  call_memos actual semantic costs (stored_empty before) available memos valid

end MicroCFTA.SourceCurrentMemoMergeQueryMemos

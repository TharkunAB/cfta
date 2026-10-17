import MicroCFTA.SourceCurrentAllocatedMergeWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedMergePhysical
import MicroCFTA.SourceCurrentMemoMergeUniformNumeric

/-!
# Initial numeric replay of the full allocated Merge worker

Instruction erasure preserves each fuel value and every constructor result.
Top-row work also retains its actual equality-field allocation. A successful
erased execution therefore gives an allocated success at the same fuels.
Stable actual graphs identify its complete returned state and merge table.
The scalar bound controls the constructor heap; equality state is retained
exactly and does not become an assumed future resource bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeNumericReplay
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedMergeGraph (Code State Memo Run Call erase top body)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
namespace Old
export SourceCurrentMemoMergeWorker (Outcome execute call)
export SourceCurrentMemoMergeUniformNumeric (workFuel selectionFuel)
end Old
namespace Worker
export SourceCurrentAllocatedMergeWorker (Outcome execute call)
end Worker
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Observation erasure retains output, constructor heap, fault, and completed memo. -/
def eraseOutcome : Worker.Outcome Output → Old.Outcome Symbol Guard Output
  | .done value state memo => .done value state.heap memo
  | .failed fault state memo => .failed fault state.heap memo

private theorem workers_erase (clear : Guard → Bool) (fuel : Nat) :
    (∀ {Output : Type} (code : Code Output) (before : State) (memo : Memo) (selection : Nat),
      eraseOutcome (Worker.execute clear fuel selection code before memo) =
        Old.execute clear top fuel selection (erase code) before.heap memo) ∧
    (∀ (input : Value Symbol Guard) (before : State) (memo : Memo) (selection : Nat),
      eraseOutcome (Worker.call clear fuel selection input before memo) =
        Old.call clear top fuel selection input before.heap memo) := by
  induction fuel with
  | zero => exact ⟨by intros; rfl, by intros; rfl⟩
  | succ fuel ih =>
      constructor
      · intro Output code before memo selection
        cases code with
        | pure value => rfl
        | work job => rfl
        | topRow symbol children => rfl
        | select inputs =>
            cases selected : SourceMergedSelection.select clear selection inputs before.heap <;>
              simp only [Worker.execute, erase, Old.execute, selected, eraseOutcome]
        | request input => exact ih.2 input before memo selection
        | bind first next =>
            have firstSame := ih.1 first before memo selection
            cases firstDone : Worker.execute clear fuel selection first before memo with
            | done value middle current =>
                rw [firstDone] at firstSame
                simp only [eraseOutcome] at firstSame
                simp only [Worker.execute, firstDone, SourceCurrentAllocatedMergeWorker.Outcome.bind,
                  erase, Old.execute, ← firstSame, SourceCurrentMemoMergeWorker.Outcome.bind]
                exact ih.1 (next value) middle current selection
            | failed fault middle current =>
                rw [firstDone] at firstSame
                simp only [eraseOutcome] at firstSame
                simp only [Worker.execute, firstDone, SourceCurrentAllocatedMergeWorker.Outcome.bind,
                  erase, Old.execute, ← firstSame, SourceCurrentMemoMergeWorker.Outcome.bind, eraseOutcome]
      · intro input before memo selection
        cases found : memo input.referenceOf with
        | some entry => simp only [Worker.call, Old.call, found, eraseOutcome]
        | none =>
            have bodySame := ih.1 (body input) before memo selection
            rw [SourceCurrentAllocatedMergeGraph.erase_body] at bodySame
            cases bodyDone : Worker.execute clear fuel selection (body input) before memo with
            | done value middle current =>
                rw [bodyDone] at bodySame
                simp only [eraseOutcome] at bodySame
                simp only [Worker.call, Old.call, found, bodyDone, SourceCurrentAllocatedMergeWorker.Outcome.bind,
                  ← bodySame, SourceCurrentMemoMergeWorker.Outcome.bind, eraseOutcome]
            | failed fault middle current =>
                rw [bodyDone] at bodySame
                simp only [eraseOutcome] at bodySame
                simp only [Worker.call, Old.call, found, bodyDone, SourceCurrentAllocatedMergeWorker.Outcome.bind,
                  ← bodySame, SourceCurrentMemoMergeWorker.Outcome.bind, eraseOutcome]

/-- Equal work and selection fuels give the exact erased instruction observation. -/
theorem execute_erase (clear : Guard → Bool) (fuel selection : Nat) (code : Code Output)
    (before : State) (memo : Memo) :
    eraseOutcome (Worker.execute clear fuel selection code before memo) =
      Old.execute clear top fuel selection (erase code) before.heap memo :=
  (workers_erase clear fuel).1 code before memo selection

/-- Equal fuels give the exact erased recursive-call observation. -/
theorem call_erase (clear : Guard → Bool) (fuel selection : Nat) (input : Value Symbol Guard)
    (before : State) (memo : Memo) :
    eraseOutcome (Worker.call clear fuel selection input before memo) =
      Old.call clear top fuel selection input before.heap memo :=
  (workers_erase clear fuel).2 input before memo selection

/-- The same successful erased fuel pair executes the actual full allocated instruction graph. -/
theorem run_replay {clear : Guard → Bool} {code : Code Output} {before after : State}
    {memo saved : Memo} {output : Output} (actual : Run clear code before memo output after saved)
    (fuel selection : Nat)
    (done : Old.execute clear top fuel selection (erase code) before.heap memo = .done output after.heap saved) :
    Worker.execute clear fuel selection code before memo = .done output after saved := by
  have agreement := execute_erase clear fuel selection code before memo
  rw [done] at agreement
  cases computed : Worker.execute clear fuel selection code before memo with
  | failed fault state current => simp only [computed, eraseOutcome] at agreement; cases agreement
  | done value state current =>
      obtain ⟨workBound, selectionBound, stable⟩ := SourceCurrentAllocatedMergeWorkerCompletion.run_complete actual
      have repeated := SourceCurrentAllocatedMergeWorkerCompletion.execute_done_stable computed
        (Nat.le_max_left fuel workBound) (Nat.le_max_left selection selectionBound)
      have expected := stable (max fuel workBound) (max selection selectionBound) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      exact computed.trans (repeated.symm.trans expected)

/-- The same successful erased fuel pair retains the actual full equality state and first winner. -/
theorem call_replay {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State}
    {memo saved : Memo} (actual : Call clear input before memo output after saved)
    (fuel selection : Nat)
    (done : Old.call clear top fuel selection input before.heap memo = .done output after.heap saved) :
    Worker.call clear fuel selection input before memo = .done output after saved := by
  have agreement := call_erase clear fuel selection input before memo
  rw [done] at agreement
  cases computed : Worker.call clear fuel selection input before memo with
  | failed fault state current => simp only [computed, eraseOutcome] at agreement; cases agreement
  | done value state current =>
      obtain ⟨workBound, selectionBound, stable⟩ := SourceCurrentAllocatedMergeWorkerCompletion.call_complete actual
      have repeated := SourceCurrentAllocatedMergeWorkerCompletion.call_done_stable computed
        (Nat.le_max_left fuel workBound) (Nat.le_max_left selection selectionBound)
      have expected := stable (max fuel workBound) (max selection selectionBound) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      exact computed.trans (repeated.symm.trans expected)

/-- Initial scalar resources replay the same allocated call at the computed worker fuels. -/
theorem of_call {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State}
    {memo saved : Memo} (actual : Call clear input before memo output after saved) (bound : Nat)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (physical : SourceCurrentMemoMergeEffects.Stored before.heap memo)
    (available : Available before.heap input) (fits : Fits bound before.heap) :
    Worker.call clear (Old.workFuel bound) (Old.selectionFuel bound) input before memo = .done output after saved ∧
      Fits (Old.workFuel bound) after.heap ∧ InternedValueMass.value output ≤ Old.workFuel bound ∧
      ∀ workExtra selectionExtra,
        Worker.call clear (Old.workFuel bound + workExtra) (Old.selectionFuel bound + selectionExtra)
          input before memo = .done output after saved := by
  have old := SourceCurrentMemoMergeUniformNumeric.of_call actual.graph bound semantic costs physical available fits
  exact ⟨call_replay actual _ _ old.1, old.2.1, old.2.2.1,
    fun workExtra selectionExtra => call_replay actual _ _ (old.2.2.2 workExtra selectionExtra)⟩

/-- Initial allocated readiness constructs the complete call and its exact numeric worker return. -/
theorem complete (clear : Guard → Bool) (input : Value Symbol Guard) (before : State) (memo : Memo) (bound : Nat)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (physical : SourceCurrentMemoMergeEffects.Stored before.heap memo)
    (available : Available before.heap input) (fits : Fits bound before.heap) :
    ∃ output after saved, Call clear input before memo output after saved ∧
      Worker.call clear (Old.workFuel bound) (Old.selectionFuel bound) input before memo = .done output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧
      SourceCurrentMemoMergeEffects.Stored after.heap saved ∧ Available after.heap output ∧
      (input.free = [] → output.free = []) ∧ Fits (Old.workFuel bound) after.heap ∧
      InternedValueMass.value output ≤ Old.workFuel bound ∧
      ∀ workExtra selectionExtra,
        Worker.call clear (Old.workFuel bound + workExtra) (Old.selectionFuel bound + selectionExtra)
          input before memo = .done output after saved := by
  obtain ⟨output, after, saved, actual, effect, retained, result, closed⟩ :=
    SourceCurrentAllocatedMergePhysical.call_complete clear input before memo ready physical available
  have checked := of_call actual bound ready.semantic ready.costs physical available fits
  exact ⟨output, after, saved, actual, checked.1, effect, retained, result, closed, checked.2.1, checked.2.2.1, checked.2.2.2⟩

end MicroCFTA.SourceCurrentAllocatedMergeNumericReplay

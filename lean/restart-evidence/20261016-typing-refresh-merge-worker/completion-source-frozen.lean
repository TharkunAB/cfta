import MicroCFTA.SourceCurrentAllocatedMergeWorkerSound
import MicroCFTA.SourceCurrentMemoMergeWorkerProofs

/-!
# Exact completion bounds for allocated merge graphs

The actual finite Run and Call graphs derive work and selection bounds.
Each larger pair returns the same output, complete allocated state, and
completed merge table. Local selections supply their own comparison bound.
No chosen result, recursive completion callback, or future invariant is
an input. These are completed serial merge workers, not pending memos.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeWorkerCompletion
open InternedConstructorTemplates
open SourceCurrentAllocatedMergeGraph (Code State Memo top body Run Call)
open SourceCurrentAllocatedMergeWorker (Outcome execute call call_hit)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "winner" => SourceCurrentMemoMergeGraph.winner
local notation "remember" => SourceCurrentMemoMergeGraph.remember
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every larger pair returns the same complete allocated instruction observation. -/
def StableRun (clear : Guard → Bool) (code : Code Output) (before : State) (memo : Memo)
    (output : Output) (after : State) (saved : Memo) : Prop :=
  ∃ workBound selectionBound, ∀ workFuel selectionFuel, workBound ≤ workFuel → selectionBound ≤ selectionFuel →
    execute clear workFuel selectionFuel code before memo = .done output after saved

/-- Every larger pair returns the same complete allocated request observation. -/
def StableCall (clear : Guard → Bool) (input : Value Symbol Guard) (before : State) (memo : Memo)
    (output : Value Symbol Guard) (after : State) (saved : Memo) : Prop :=
  ∃ workBound selectionBound, ∀ workFuel selectionFuel, workBound ≤ workFuel → selectionBound ≤ selectionFuel →
    call clear workFuel selectionFuel input before memo = .done output after saved

private theorem complete {clear : Guard → Bool} :
    (∀ {Output} (code : Code Output) before memo output after saved, Run clear code before memo output after saved →
      StableRun clear code before memo output after saved) ∧
    (∀ (input : Value Symbol Guard) before memo output after saved, Call clear input before memo output after saved →
      StableCall clear input before memo output after saved) := by
  have pureCase : ∀ {Output} (value : Output) (state : State) (memo : Memo),
      StableRun clear (.pure value) state memo value state memo := by
    intro Output value state memo
    refine ⟨1, 0, ?_⟩
    intro workFuel selectionFuel enough _
    cases workFuel with
    | zero => omega
    | succ => rfl
  have workCase : ∀ {Output} (job : Work Symbol Guard Output) (state : State) (memo : Memo),
      StableRun clear (.work job) state memo (run job state.heap).1 ⟨(run job state.heap).2, state.equality⟩ memo := by
    intro Output job state memo
    refine ⟨1, 0, ?_⟩
    intro workFuel selectionFuel enough _
    cases workFuel with
    | zero => omega
    | succ => rfl
  have topCase : ∀ (symbol : Symbol) (children : List (Value Symbol Guard)) (state : State) (memo : Memo),
      StableRun clear (.topRow symbol children) state memo (run (makeEdge symbol top children) state.heap).1
        ⟨(run (makeEdge symbol top children) state.heap).2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩ memo := by
    intro symbol children state memo
    refine ⟨1, 0, ?_⟩
    intro workFuel selectionFuel enough _
    cases workFuel with
    | zero => omega
    | succ => rfl
  have selectCase : ∀ fuel (inputs : List (Value Symbol Guard)) (before : State) values heap memo,
      SourceMergedSelection.select clear fuel inputs before.heap = .done values heap →
      StableRun clear (.select inputs) before memo values ⟨heap, before.equality⟩ memo := by
    intro fuel inputs before values heap memo actual
    refine ⟨1, fuel, ?_⟩
    intro workFuel selectionFuel enough selectionEnough
    cases workFuel with
    | zero => omega
    | succ =>
        simp only [execute, SourceCurrentMemoMergeWorkerProofs.selection_stable clear fuel selectionFuel inputs
          before.heap values heap actual selectionEnough]
  have requestCase : ∀ (input : Value Symbol Guard) before memo output after saved,
      Call clear input before memo output after saved → StableCall clear input before memo output after saved →
      StableRun clear (.request input) before memo output after saved := by
    intro input before memo output after saved _ stable
    obtain ⟨work, selection, done⟩ := stable
    refine ⟨work + 1, selection, ?_⟩
    intro workFuel selectionFuel enough selectionEnough
    cases workFuel with
    | zero => omega
    | succ remaining => exact done remaining selectionFuel (by omega) selectionEnough
  have bindCase : ∀ {Input Output : Type} (first : Code Input) (next : Input → Code Output)
      before memo (value : Input) middle current (output : Output) after saved,
      Run clear first before memo value middle current → Run clear (next value) middle current output after saved →
      StableRun clear first before memo value middle current → StableRun clear (next value) middle current output after saved →
      StableRun clear (.bind first next) before memo output after saved := by
    intro Input Output first next before memo value middle current output after saved _ _ firstStable laterStable
    obtain ⟨firstWork, firstSelection, firstDone⟩ := firstStable
    obtain ⟨laterWork, laterSelection, laterDone⟩ := laterStable
    refine ⟨max firstWork laterWork + 1, max firstSelection laterSelection, ?_⟩
    intro workFuel selectionFuel enough selectionEnough
    cases workFuel with
    | zero => omega
    | succ remaining =>
        simp only [execute, firstDone remaining selectionFuel (by omega) (by omega), Outcome.bind]
        exact laterDone remaining selectionFuel (by omega) (by omega)
  have hitCase : ∀ (input : Value Symbol Guard) before memo entry, memo input.referenceOf = some entry →
      StableCall clear input before memo entry.result before memo := by
    intro input before memo entry found
    refine ⟨1, 0, ?_⟩
    intro workFuel selectionFuel enough _
    cases workFuel with
    | zero => omega
    | succ => exact call_hit _ _ _ _ _ _ _ found
  have missCase : ∀ (input : Value Symbol Guard) before memo candidate after current,
      memo input.referenceOf = none → Run clear (body input) before memo candidate after current →
      StableRun clear (body input) before memo candidate after current →
      StableCall clear input before memo (winner current input candidate).result after (remember current input candidate) := by
    intro input before memo candidate after current absent _ stable
    obtain ⟨work, selection, done⟩ := stable
    refine ⟨work + 1, selection, ?_⟩
    intro workFuel selectionFuel enough selectionEnough
    cases workFuel with
    | zero => omega
    | succ remaining => simp only [call, absent, done remaining selectionFuel (by omega) selectionEnough, Outcome.bind]
  constructor
  · intro Output code before memo output after saved actual
    exact Run.rec
      (motive_1 := fun {_} code before memo output after saved _ => StableRun clear code before memo output after saved)
      (motive_2 := fun input before memo output after saved _ => StableCall clear input before memo output after saved)
      pureCase workCase topCase
      (by intros; apply selectCase; assumption)
      (by intros; apply requestCase <;> assumption)
      (by intros; apply bindCase <;> assumption)
      (by intros; apply hitCase; assumption)
      (by intros; apply missCase <;> assumption) actual
  · intro input before memo output after saved actual
    exact Call.rec
      (motive_1 := fun {_} code before memo output after saved _ => StableRun clear code before memo output after saved)
      (motive_2 := fun input before memo output after saved _ => StableCall clear input before memo output after saved)
      pureCase workCase topCase
      (by intros; apply selectCase; assumption)
      (by intros; apply requestCase <;> assumption)
      (by intros; apply bindCase <;> assumption)
      (by intros; apply hitCase; assumption)
      (by intros; apply missCase <;> assumption) actual

/-- Every actual finite allocated instruction graph derives stable exact worker bounds. -/
theorem run_complete {clear : Guard → Bool} {code : Code Output} {before after : State} {memo saved : Memo} {output : Output}
    (actual : Run clear code before memo output after saved) : StableRun clear code before memo output after saved :=
  complete.1 code before memo output after saved actual

/-- Every actual finite allocated request graph derives stable exact worker bounds. -/
theorem call_complete {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State} {memo saved : Memo}
    (actual : Call clear input before memo output after saved) : StableCall clear input before memo output after saved :=
  complete.2 input before memo output after saved actual

/-- A shared upper bound supplies both instruction and selection fuel. -/
theorem run_uniform {clear : Guard → Bool} {code : Code Output} {before after : State} {memo saved : Memo} {output : Output}
    (actual : Run clear code before memo output after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel → execute clear fuel fuel code before memo = .done output after saved := by
  obtain ⟨work, selection, done⟩ := run_complete actual
  exact ⟨max work selection, fun fuel enough => done fuel fuel
    (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) enough)⟩

/-- A shared upper bound supplies a whole allocated request and all its selections. -/
theorem call_uniform {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State} {memo saved : Memo}
    (actual : Call clear input before memo output after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel → call clear fuel fuel input before memo = .done output after saved := by
  obtain ⟨work, selection, done⟩ := call_complete actual
  exact ⟨max work selection, fun fuel enough => done fuel fuel
    (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) enough)⟩

private theorem done_stable (clear : Guard → Bool) (workFuel : Nat) :
    (∀ {Output} (code : Code Output) before memo output after saved selectionFuel largerWork largerSelection,
      execute clear workFuel selectionFuel code before memo = .done output after saved →
      workFuel ≤ largerWork → selectionFuel ≤ largerSelection →
      execute clear largerWork largerSelection code before memo = .done output after saved) ∧
    (∀ (input : Value Symbol Guard) before memo output after saved selectionFuel largerWork largerSelection,
      call clear workFuel selectionFuel input before memo = .done output after saved →
      workFuel ≤ largerWork → selectionFuel ≤ largerSelection →
      call clear largerWork largerSelection input before memo = .done output after saved) := by
  induction workFuel with
  | zero =>
      constructor
      · intro _ code before memo output after saved selectionFuel largerWork largerSelection impossible
        cases impossible
      · intro input before memo output after saved selectionFuel largerWork largerSelection impossible
        cases impossible
  | succ workFuel ih =>
      constructor
      · intro Output code before memo output after saved selectionFuel largerWork largerSelection actual enough selectionEnough
        cases largerWork with
        | zero => omega
        | succ remaining =>
            cases code with
            | pure value => simp only [execute] at actual; cases actual; rfl
            | work job => simp only [execute] at actual; cases actual; rfl
            | topRow symbol children => simp only [execute] at actual; cases actual; rfl
            | select inputs =>
                cases selected : SourceMergedSelection.select clear selectionFuel inputs before.heap with
                | done values heap =>
                    simp only [execute, selected] at actual
                    cases actual
                    simp only [execute, SourceCurrentMemoMergeWorkerProofs.selection_stable clear selectionFuel largerSelection
                      inputs before.heap output heap selected selectionEnough]
                | failed fault heap => simp only [execute, selected] at actual; cases actual
            | request input =>
                exact ih.2 input before memo output after saved selectionFuel remaining largerSelection actual (by omega) selectionEnough
            | bind first next =>
                obtain ⟨value, middle, current, firstDone, laterDone⟩ :=
                  (SourceCurrentAllocatedMergeWorkerSound.bind_done_iff _ _ output after saved).mp actual
                have firstLarger := ih.1 first before memo value middle current selectionFuel remaining largerSelection
                  firstDone (by omega) selectionEnough
                have laterLarger := ih.1 (next value) middle current output after saved selectionFuel remaining largerSelection
                  laterDone (by omega) selectionEnough
                simpa only [execute, firstLarger, Outcome.bind] using laterLarger
      · intro input before memo output after saved selectionFuel largerWork largerSelection actual enough selectionEnough
        cases largerWork with
        | zero => omega
        | succ remaining =>
            cases found : memo input.referenceOf with
            | some entry =>
                simp only [call, found] at actual
                cases actual
                simp only [call, found]
            | none =>
                simp only [call, found] at actual
                obtain ⟨candidate, middle, current, bodyDone, returned⟩ :=
                  (SourceCurrentAllocatedMergeWorkerSound.bind_done_iff _ _ output after saved).mp actual
                have bodyLarger := ih.1 (body input) before memo candidate middle current selectionFuel remaining largerSelection
                  bodyDone (by omega) selectionEnough
                simpa only [call, found, bodyLarger, Outcome.bind] using returned

/-- Increasing either fuel preserves the literal successful instruction observation. -/
theorem execute_done_stable {clear : Guard → Bool} {code : Code Output} {before after : State}
    {memo saved : Memo} {output : Output} {workFuel selectionFuel largerWork largerSelection : Nat}
    (actual : execute clear workFuel selectionFuel code before memo = .done output after saved)
    (workEnough : workFuel ≤ largerWork) (selectionEnough : selectionFuel ≤ largerSelection) :
    execute clear largerWork largerSelection code before memo = .done output after saved :=
  (done_stable clear workFuel).1 code before memo output after saved selectionFuel largerWork largerSelection
    actual workEnough selectionEnough

/-- Increasing either fuel preserves the exact allocated request state and winner. -/
theorem call_done_stable {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State}
    {memo saved : Memo} {workFuel selectionFuel largerWork largerSelection : Nat}
    (actual : call clear workFuel selectionFuel input before memo = .done output after saved)
    (workEnough : workFuel ≤ largerWork) (selectionEnough : selectionFuel ≤ largerSelection) :
    call clear largerWork largerSelection input before memo = .done output after saved :=
  (done_stable clear workFuel).2 input before memo output after saved selectionFuel largerWork largerSelection
    actual workEnough selectionEnough

/-- Successful allocated instruction executions are exactly the finite actual graphs. -/
theorem execute_done_iff {clear : Guard → Bool} {code : Code Output} {before after : State}
    {memo saved : Memo} {output : Output} :
    (∃ workFuel selectionFuel, execute clear workFuel selectionFuel code before memo = .done output after saved) ↔
      Run clear code before memo output after saved := by
  constructor
  · rintro ⟨_, _, actual⟩
    exact SourceCurrentAllocatedMergeWorkerSound.execute_sound actual
  · intro actual
    obtain ⟨work, selection, done⟩ := run_complete actual
    exact ⟨work, selection, done work selection (Nat.le_refl _) (Nat.le_refl _)⟩

/-- Successful allocated requests are exactly finite hit and recursive miss graphs. -/
theorem call_done_iff {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State} {memo saved : Memo} :
    (∃ workFuel selectionFuel, call clear workFuel selectionFuel input before memo = .done output after saved) ↔
      Call clear input before memo output after saved := by
  constructor
  · rintro ⟨_, _, actual⟩
    exact SourceCurrentAllocatedMergeWorkerSound.call_sound actual
  · intro actual
    obtain ⟨work, selection, done⟩ := call_complete actual
    exact ⟨work, selection, done work selection (Nat.le_refl _) (Nat.le_refl _)⟩

end MicroCFTA.SourceCurrentAllocatedMergeWorkerCompletion

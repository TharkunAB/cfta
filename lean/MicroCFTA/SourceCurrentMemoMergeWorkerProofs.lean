import MicroCFTA.SourceCurrentMemoMergeWorker
import MicroCFTA.SourceMergedComparisonStability

/-!
# Exact graph correspondence and bounds for the memo-aware worker

Completed observations derive the literal Run and Call graph. Every finite
graph derives stable work and comparison bounds. The comparison bound is
computed from its local selection receipts. No heap invariant or completed
recursive callback is required for this operational correspondence.
-/
namespace MicroCFTA.SourceCurrentMemoMergeWorkerProofs
open InternedConstructorTemplates SourceCurrentMemoMergeGraph SourceCurrentMemoMergeWorker
open MergedSourceComparison (Result)
open MergedComparisonStability (Refines bind_refines)

private theorem any_refines [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel extra : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) :
    Refines (SourceMergedSelection.anyAccepts clear fuel narrow wides)
      (SourceMergedSelection.anyAccepts clear (fuel + extra) narrow wides) := by
  induction wides with
  | nil => exact .refl _
  | cons wide rest ih =>
      by_cases closed : narrow.free = []
      · simp only [SourceMergedSelection.anyAccepts, closed, ite_true]
        exact bind_refines _ _ _ _ (SourceMergedComparisonStability.check_refines clear fuel extra [] wide narrow)
          (fun accepted => by cases accepted with | false => exact ih | true => exact .refl _)
      · simp only [SourceMergedSelection.anyAccepts, closed, ite_false]
        exact .refl _

private theorem retain_refines [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel extra : Nat) (recursive inputs : List (Value Symbol Guard)) :
    Refines (SourceMergedSelection.retain clear fuel recursive inputs)
      (SourceMergedSelection.retain clear (fuel + extra) recursive inputs) := by
  induction inputs with
  | nil => exact .refl _
  | cons child rest ih =>
      by_cases recursiveChild : MergedPhysicalGroupColumns.closedMu child = true
      · simp only [SourceMergedSelection.retain, recursiveChild, ite_true]
        exact bind_refines _ _ _ _ ih (fun _ => .refl _)
      · simp only [SourceMergedSelection.retain, recursiveChild]
        exact bind_refines _ _ _ _ (any_refines clear fuel extra child recursive) (fun _ =>
          bind_refines _ _ _ _ ih (fun _ => .refl _))

/-- Extra comparison fuel preserves every completed selection and its exact returned heap. -/
theorem selection_refines [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel extra : Nat) (inputs : List (Value Symbol Guard)) :
    Refines (SourceMergedSelection.select clear fuel inputs)
      (SourceMergedSelection.select clear (fuel + extra) inputs) :=
  bind_refines _ _ _ _ (retain_refines clear fuel extra _ inputs) (fun _ => .refl _)

/-- A local completed comparison bound remains valid at every larger shared bound. -/
theorem selection_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (bound fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear bound inputs before = .done values after) (larger : bound ≤ fuel) :
    SourceMergedSelection.select clear fuel inputs before = .done values after := by
  have same : bound + (fuel - bound) = fuel := by omega
  simpa only [same] using selection_refines clear bound (fuel - bound) inputs before values after done

/-- A completed bind retains the actual value, heap and result table of its prefix. -/
theorem bind_done_iff (first : Outcome Symbol Guard Input)
    (next : Input → State Symbol Guard → Memo Symbol Guard → Outcome Symbol Guard Output)
    (output : Output) (after : State Symbol Guard) (saved : Memo Symbol Guard) :
    first.bind next = .done output after saved ↔
      ∃ value middle current, first = .done value middle current ∧ next value middle current = .done output after saved := by
  cases first with
  | done value heap memo =>
      constructor
      · intro actual; exact ⟨value, heap, memo, rfl, actual⟩
      · rintro ⟨_, _, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, _, impossible, _⟩; cases impossible

private theorem sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (fuel : Nat) :
    (∀ {Output : Type} (code : Code Symbol Guard Output) before memo output after saved selectionFuel,
      execute clear top fuel selectionFuel code before memo = .done output after saved →
        Run clear top code before memo output after saved) ∧
    (∀ (input : Value Symbol Guard) before memo output after saved selectionFuel,
      call clear top fuel selectionFuel input before memo = .done output after saved →
        Call clear top input before memo output after saved) := by
  induction fuel with
  | zero =>
      constructor
      · intro _ code before memo output after saved selectionFuel impossible; cases impossible
      · intro input before memo output after saved selectionFuel impossible; cases impossible
  | succ fuel ih =>
      constructor
      · intro Output code before memo output after saved selectionFuel done
        cases code with
        | pure value =>
            simp only [execute] at done
            cases done
            exact .pure _ _ _
        | work job =>
            simp only [execute] at done
            cases done
            exact .work _ _ _
        | select inputs =>
            simp only [execute] at done
            cases selected : SourceMergedSelection.select clear selectionFuel inputs before with
            | done values heap =>
                simp only [selected] at done
                cases done
                exact .select selectionFuel selected
            | failed => simp only [selected] at done; cases done
        | request input => exact .request (ih.2 input before memo output after saved selectionFuel done)
        | bind first next =>
            obtain ⟨value, middle, current, firstDone, laterDone⟩ :=
              (bind_done_iff _ _ output after saved).mp done
            exact .bind (ih.1 first before memo value middle current selectionFuel firstDone)
              (ih.1 (next value) middle current output after saved selectionFuel laterDone)
      · intro input before memo output after saved selectionFuel done
        cases found : memo input.referenceOf with
        | some entry =>
            simp only [call, found] at done
            cases done
            exact .hit found
        | none =>
            simp only [call, found] at done
            obtain ⟨candidate, heap, current, bodyDone, returned⟩ := (bind_done_iff _ _ output after saved).mp done
            cases returned
            exact .miss found (ih.1 (body top input) before memo candidate _ current selectionFuel bodyDone)

/-- Every completed executable instruction has the same actual graph output, heap and table. -/
theorem execute_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    {fuel selectionFuel : Nat} (done : execute clear top fuel selectionFuel code before memo = .done output after saved) :
    Run clear top code before memo output after saved := (sound clear top fuel).1 code before memo output after saved selectionFuel done

/-- Every completed executable request derives the literal hit or recursive miss graph. -/
theorem call_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {fuel selectionFuel : Nat}
    (done : call clear top fuel selectionFuel input before memo = .done output after saved) :
    Call clear top input before memo output after saved := (sound clear top fuel).2 input before memo output after saved selectionFuel done

/-- Every larger pair of bounds returns the same complete instruction observation. -/
def StableRun [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (output : Output)
    (after : State Symbol Guard) (saved : Memo Symbol Guard) : Prop :=
  ∃ workBound selectionBound, ∀ workFuel selectionFuel, workBound ≤ workFuel → selectionBound ≤ selectionFuel →
    execute clear top workFuel selectionFuel code before memo = .done output after saved

/-- Every larger pair of bounds returns the same complete request observation. -/
def StableCall [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (output : Value Symbol Guard)
    (after : State Symbol Guard) (saved : Memo Symbol Guard) : Prop :=
  ∃ workBound selectionBound, ∀ workFuel selectionFuel, workBound ≤ workFuel → selectionBound ≤ selectionFuel →
    call clear top workFuel selectionFuel input before memo = .done output after saved

private theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} :
    (∀ {Output} (code : Code Symbol Guard Output) before memo output after saved, Run clear top code before memo output after saved →
      StableRun clear top code before memo output after saved) ∧
    (∀ (input : Value Symbol Guard) before memo output after saved, Call clear top input before memo output after saved →
      StableCall clear top input before memo output after saved) := by
  have pureCase : ∀ {Output} (value : Output) (state : State Symbol Guard) (memo : Memo Symbol Guard),
      StableRun clear top (.pure value) state memo value state memo := by
    intro Output value state memo
    refine ⟨1, 0, ?_⟩
    intro workFuel selectionFuel workEnough _
    cases workFuel with
    | zero => omega
    | succ => rfl
  have workCase : ∀ {Output} (job : Work Symbol Guard Output) state memo,
      StableRun clear top (.work job) state memo (run job state).1 (run job state).2 memo := by
    intro Output job state memo
    refine ⟨1, 0, ?_⟩
    intro workFuel selectionFuel workEnough _
    cases workFuel with
    | zero => omega
    | succ => rfl
  have selectCase : ∀ fuel (inputs : List (Value Symbol Guard)) before values after memo,
      SourceMergedSelection.select clear fuel inputs before = .done values after →
      StableRun clear top (.select inputs) before memo values after memo := by
    intro fuel inputs before values after memo actual
    refine ⟨1, fuel, ?_⟩
    intro workFuel selectionFuel workEnough selectionEnough
    cases workFuel with
    | zero => omega
    | succ => simp only [execute, selection_stable clear fuel selectionFuel inputs before values after actual selectionEnough]
  have requestCase : ∀ (input : Value Symbol Guard) before memo output after saved,
      Call clear top input before memo output after saved → StableCall clear top input before memo output after saved →
      StableRun clear top (.request input) before memo output after saved := by
    intro input before memo output after saved _ stable
    obtain ⟨work, selection, done⟩ := stable
    refine ⟨work + 1, selection, ?_⟩
    intro workFuel selectionFuel workEnough selectionEnough
    cases workFuel with
    | zero => omega
    | succ remaining => exact done remaining selectionFuel (by omega) selectionEnough
  have bindCase : ∀ {Input Output : Type} (first : Code Symbol Guard Input) (next : Input → Code Symbol Guard Output)
      before memo (value : Input) middle current (output : Output) after saved,
      Run clear top first before memo value middle current → Run clear top (next value) middle current output after saved →
      StableRun clear top first before memo value middle current → StableRun clear top (next value) middle current output after saved →
      StableRun clear top (.bind first next) before memo output after saved := by
    intro Input Output first next before memo value middle current output after saved _ _ firstStable laterStable
    obtain ⟨firstWork, firstSelection, firstDone⟩ := firstStable
    obtain ⟨laterWork, laterSelection, laterDone⟩ := laterStable
    refine ⟨max firstWork laterWork + 1, max firstSelection laterSelection, ?_⟩
    intro workFuel selectionFuel workEnough selectionEnough
    cases workFuel with
    | zero => omega
    | succ remaining =>
        simp only [execute, firstDone remaining selectionFuel (by omega) (by omega), Outcome.bind]
        exact laterDone remaining selectionFuel (by omega) (by omega)
  have hitCase : ∀ (input : Value Symbol Guard) before memo entry, memo input.referenceOf = some entry →
      StableCall clear top input before memo entry.result before memo := by
    intro input before memo entry found
    refine ⟨1, 0, ?_⟩
    intro workFuel selectionFuel workEnough _
    cases workFuel with
    | zero => omega
    | succ => exact call_hit _ _ _ _ _ _ _ _ found
  have missCase : ∀ (input : Value Symbol Guard) before memo candidate after current,
      memo input.referenceOf = none → Run clear top (body top input) before memo candidate after current →
      StableRun clear top (body top input) before memo candidate after current →
      StableCall clear top input before memo (winner current input candidate).result after (remember current input candidate) := by
    intro input before memo candidate after current absent _ stable
    obtain ⟨work, selection, done⟩ := stable
    refine ⟨work + 1, selection, ?_⟩
    intro workFuel selectionFuel workEnough selectionEnough
    cases workFuel with
    | zero => omega
    | succ remaining => simp only [call, absent, done remaining selectionFuel (by omega) selectionEnough, Outcome.bind]
  constructor
  · intro Output code before memo output after saved actual
    exact Run.rec
      (motive_1 := fun {_} code before memo output after saved _ => StableRun clear top code before memo output after saved)
      (motive_2 := fun input before memo output after saved _ => StableCall clear top input before memo output after saved)
      pureCase workCase
      (by intros; apply selectCase; assumption)
      (by intros; apply requestCase <;> assumption)
      (by intros; apply bindCase <;> assumption)
      (by intros; apply hitCase; assumption)
      (by intros; apply missCase <;> assumption) actual
  · intro input before memo output after saved actual
    exact Call.rec
      (motive_1 := fun {_} code before memo output after saved _ => StableRun clear top code before memo output after saved)
      (motive_2 := fun input before memo output after saved _ => StableCall clear top input before memo output after saved)
      pureCase workCase
      (by intros; apply selectCase; assumption)
      (by intros; apply requestCase <;> assumption)
      (by intros; apply bindCase <;> assumption)
      (by intros; apply hitCase; assumption)
      (by intros; apply missCase <;> assumption) actual

/-- Every actual finite instruction graph supplies stable shared worker and selection bounds. -/
theorem run_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) : StableRun clear top code before memo output after saved :=
  complete.1 code before memo output after saved actual

/-- Every actual finite request graph supplies stable bounds without a recursive completion premise. -/
theorem call_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) : StableCall clear top input before memo output after saved :=
  complete.2 input before memo output after saved actual

/-- Completed executable instructions are exactly the actual finite instruction graph. -/
theorem execute_done_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output} :
    (∃ fuel selectionFuel, execute clear top fuel selectionFuel code before memo = .done output after saved) ↔
      Run clear top code before memo output after saved := by
  constructor
  · rintro ⟨_, _, done⟩; exact execute_sound done
  · intro actual
    obtain ⟨work, selection, done⟩ := run_complete actual
    exact ⟨work, selection, done work selection (Nat.le_refl _) (Nat.le_refl _)⟩

/-- Completed executable requests are exactly the actual finite hit and miss graph. -/
theorem call_done_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} :
    (∃ fuel selectionFuel, call clear top fuel selectionFuel input before memo = .done output after saved) ↔
      Call clear top input before memo output after saved := by
  constructor
  · rintro ⟨_, _, done⟩; exact call_sound done
  · intro actual
    obtain ⟨work, selection, done⟩ := call_complete actual
    exact ⟨work, selection, done work selection (Nat.le_refl _) (Nat.le_refl _)⟩

/-- One derived bound suffices for instruction fuel and every reached local selection. -/
theorem run_uniform [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel → execute clear top fuel fuel code before memo = .done output after saved := by
  obtain ⟨work, selection, done⟩ := run_complete actual
  exact ⟨max work selection, fun fuel enough => done fuel fuel
    (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) enough)⟩

/-- One derived bound suffices for a whole request and all recursive comparison sites. -/
theorem call_uniform [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel → call clear top fuel fuel input before memo = .done output after saved := by
  obtain ⟨work, selection, done⟩ := call_complete actual
  exact ⟨max work selection, fun fuel enough => done fuel fuel
    (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) enough)⟩

end MicroCFTA.SourceCurrentMemoMergeWorkerProofs

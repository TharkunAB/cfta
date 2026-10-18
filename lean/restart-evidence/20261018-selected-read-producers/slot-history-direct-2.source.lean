import MicroCFTA.SourceCurrentActualSharedLeafEvents
import MicroCFTA.SourceCurrentActualClassDispatch

/-!
# Causal target-slot writers through actual selected edits

History records only target-table preservation and actual first writes.
It asserts no semantic law about native cells or target results. Actual
completed workers construct this history from their exact input states.
An initially absent slot therefore recovers its earlier literal target
call, with the same captured class and original forest. Each new class
starts its own empty slots. Native and merge tables can already be warm.
-/
namespace MicroCFTA.SourceCurrentActualTargetSlotHistory
open Cache InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedTargetState
open SourceCurrentAllocatedSharedEditWorker (Outcome children rows edit editList)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
variable {width : Nat}

/-- Target history records actual missing-slot calls and target-preserving state changes. -/
inductive History [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h m s n : Nat) (record : Record) (originals : List Node) : Shared width → Shared width → Prop where
  /-- An unchanged target table has no new writer. -/
  | refl (state : Shared width) : History p h m s n record originals state state
  /-- Changes to other state fields retain every target entry. -/
  | retained {before middle after : Shared width}
      (earlier : History p h m s n record originals before middle)
      (same : after.targets = middle.targets) : History p h m s n record originals before after
  /-- A literal completed missing-slot target installs its first value. -/
  | stored {before middle : Shared width} {path : Path} {value : Node}
      {checked : Checked width} {saved : Memo}
      (earlier : History p h m s n record originals before middle)
      (missing : middle.targets path = none)
      (actual : SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) middle.checked middle.memo =
          .done value checked saved) :
      History p h m s n record originals before (store middle path value checked saved)

private theorem bind_done (first : Outcome width A)
    (next : A → Shared width → Outcome width B) {value : B} {after : Shared width}
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {p h m s n : Nat} {record : Record} {originals : List Node}

/-- Consecutive actual slot histories retain the same class and captured forest. -/
theorem History.trans {before middle after : Shared width}
    (first : History p h m s n record originals before middle)
    (last : History p h m s n record originals middle after) :
    History p h m s n record originals before after := by
  induction last with
  | refl => exact first
  | retained _ same ih => exact .retained ih same
  | stored _ missing actual ih => exact .stored ih missing actual

/-- A completed first write cannot replace a previously present target. -/
theorem History.keeps {before after : Shared width}
    (history : History p h m s n record originals before after) : Extends before.targets after.targets := by
  induction history with
  | refl => exact extends_refl _
  | retained _ same ih => simpa only [same] using ih
  | @stored middle path value checked saved earlier missing actual ih =>
    intro other previous present
    have known := ih other previous present
    have different : other ≠ path := by intro equal; subst other; rw [missing] at known; cases known
    simpa [store,put,different] using known

/-- A newly present target recovers its actual first writer and both surrounding slot histories. -/
theorem History.writer {before after : Shared width}
    (history : History p h m s n record originals before after)
    {path : Path} {value : Node} (missing : before.targets path = none)
    (present : after.targets path = some value) :
    ∃ (writer : Shared width) (checked : Checked width) (saved : Memo),
      History p h m s n record originals before writer ∧ writer.targets path = none ∧
      SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) writer.checked writer.memo =
          .done value checked saved ∧
      History p h m s n record originals (store writer path value checked saved) after := by
  induction history with
  | refl => rw [missing] at present; cases present
  | @retained middle after earlier same ih =>
      obtain ⟨writer,checked,saved,first,absent,actual,last⟩ := ih (by simpa only [same] using present)
      exact ⟨writer,checked,saved,first,absent,actual,.retained last same⟩
  | @stored middle written target checked saved earlier absent actual ih =>
      by_cases equal : path = written
      · subst written
        have same : target = value := Option.some.inj (by simpa [store,put] using present)
        subst target
        exact ⟨middle,checked,saved,earlier,absent,actual,.refl _⟩
      · have previous : middle.targets path = some value := by simpa [store,put,equal] using present
        obtain ⟨writer,firstChecked,firstSaved,first,wasMissing,called,last⟩ := ih previous
        exact ⟨writer,firstChecked,firstSaved,first,wasMissing,called,.stored last absent actual⟩

/-- Literal force success constructs its own target history without a supplied writer. -/
theorem force {path : Path} {before after : Shared width} {value : Node}
    (actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before =
      .done value after) : History p h m s n record originals before after := by
  rcases SourceCurrentActualSharedLeafEvents.force actual with ⟨_,rfl⟩ | ⟨missing,checked,saved,called,rfl⟩
  · exact .refl _
  · exact .stored (.refl _) missing called

/-- Actual leaf execution preserves the target history through its exact native return. -/
theorem leaf {path : Path} {input result : Node} {before after : Shared width}
    (actual : SourceCurrentAllocatedSharedEditWorker.leaf p h m s n record originals path input before =
      .done result after) : History p h m s n record originals before after := by
  obtain ⟨target,middle,checked,forced,_queried,rfl,_⟩ := SourceCurrentActualSharedLeafEvents.leaf actual
  exact .retained (force forced) rfl

private theorem work_history (request : Work Symbol Guard A) {before after : Shared width} {value : A}
    (actual : SourceCurrentAllocatedSharedEditWorker.work request before = .done value after) :
    History p h m s n record originals before after := by
  simp only [SourceCurrentAllocatedSharedEditWorker.work] at actual
  cases actual
  exact .retained (.refl _) rfl

private theorem head_history {readFuel : Nat} {input result : Node} {before after : Shared width}
    (actual : SourceCurrentAllocatedSharedEditWorker.head readFuel input before = .done result after) :
    History p h m s n record originals before after := by
  unfold SourceCurrentAllocatedSharedEditWorker.head at actual
  split at actual <;> cases actual
  exact .retained (.refl _) rfl

/-- Every completed child loop composes only the histories of its actual selected calls. -/
theorem children_history
    (recur : Edits Path → Node → Shared width → Outcome width Node)
    (retains : ∀ edits value before result after, recur edits value before = .done result after →
      History p h m s n record originals before after)
    {entries : List (Int × Edits Path)} {index : Nat} {values results : List Node}
    {before after : Shared width}
    (actual : children recur entries index values before = .done results after) :
    History p h m s n record originals before after := by
  induction values generalizing index results before after with
  | nil => simp only [children] at actual; cases actual; exact .refl _
  | cons value values ih =>
      cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
      | none =>
          simp only [children,found] at actual
          obtain ⟨tail,last,rest,done⟩ := bind_done _ _ actual
          cases done
          exact ih rest
      | some edits =>
          simp only [children,found] at actual
          obtain ⟨output,middle,first,rest⟩ := bind_done _ _ actual
          obtain ⟨tail,last,rest,done⟩ := bind_done _ _ rest
          cases done
          exact (retains edits value before output middle first).trans (ih rest)

/-- Actual row order retains the same target slots across reconstructed edges. -/
theorem rows_history
    (recur : Edits Path → Node → Shared width → Outcome width Node)
    (retains : ∀ edits value before result after, recur edits value before = .done result after →
      History p h m s n record originals before after)
    {entries : List (Int × Edits Path)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : Shared width}
    (actual : rows recur entries edges before = .done results after) :
    History p h m s n record originals before after := by
  induction edges generalizing results before after with
  | nil => simp only [rows] at actual; cases actual; exact .refl _
  | cons edge edges ih =>
      simp only [rows] at actual
      obtain ⟨values,middle,first,rest⟩ := bind_done _ _ actual
      obtain ⟨rebuilt,afterEdge,constructed,rest⟩ := bind_done _ _ rest
      obtain ⟨tail,last,later,done⟩ := bind_done _ _ rest
      cases done
      exact (children_history recur retains first).trans ((work_history _ constructed).trans (ih later))

/-- The actual edit derives all target writers, including repeated paths below recursive heads. -/
theorem edit_history {e : Nat} {edits : Edits Path} {input result : Node} {before after : Shared width}
    (actual : edit record originals e p h m s n edits input before = .done result after) :
    History p h m s n record originals before after := by
  induction e generalizing edits input result before after with
  | zero => simp only [edit] at actual; cases actual
  | succ e ih =>
      cases edits with
      | editAt path => exact leaf actual
      | editBelow entries =>
          cases input with
          | empty => simp only [edit] at actual; cases actual; exact .refl _
          | reference => simp only [edit] at actual; cases actual
          | node identity edges free used =>
              simp only [edit] at actual
              obtain ⟨rebuilt,middle,first,last⟩ := bind_done _ _ actual
              exact (rows_history _ (fun _ _ _ _ _ => ih) first).trans (work_history _ last)
          | mu | union =>
              simp only [edit] at actual
              obtain ⟨exposed,middle,first,last⟩ := bind_done _ _ actual
              exact (head_history first).trans (ih last)

/-- A compiled child-list execution derives target history from the exact shared start. -/
theorem edit_list {e : Nat} {edits : Edits Path} {values results : List Node} {before after : Shared width}
    (actual : editList (edit record originals e p h m s n) edits values before = .done results after) :
    History p h m s n record originals before after := by
  cases edits with
  | editAt => simp only [editList] at actual; cases actual; exact .refl _
  | editBelow entries => exact children_history _ (fun _ _ _ _ _ => edit_history) actual

/-- Each actual class derives its returned shared state and history from freshly empty target slots. -/
theorem class_call {e : Nat} {values results : List Node} {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo =
      .done results after saved) :
    ∃ shared : Shared width, shared.checked = after ∧ shared.memo = saved ∧
      editList (edit record values e p h m s n) (SourceCurrentAllocatedClassEditPlan.compiled record) values
        (initial before memo) = .done results shared ∧
      History p h m s n record values (initial before memo) shared := by
  unfold SourceCurrentAllocatedClassWorker.runClass at actual
  cases completed : editList (edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values (initial before memo) with
  | failed => simp only [completed] at actual; cases actual
  | done output shared =>
      simp only [completed] at actual
      cases actual
      exact ⟨shared,rfl,rfl,rfl,edit_list completed⟩

/-- Actual force success recovers its exact earlier target writer from an initially absent slot. -/
theorem force_writer {initialState before after : Shared width} {path : Path} {value : Node}
    (earlier : History p h m s n record originals initialState before)
    (missing : initialState.targets path = none)
    (actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before =
      .done value after) :
    ∃ (writer : Shared width) (checked : Checked width) (saved : Memo),
      History p h m s n record originals initialState writer ∧ writer.targets path = none ∧
      SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) writer.checked writer.memo =
          .done value checked saved ∧
      History p h m s n record originals (store writer path value checked saved) after := by
  have present : after.targets path = some value := by
    rcases SourceCurrentActualSharedLeafEvents.force actual with ⟨known,rfl⟩ | ⟨_,checked,saved,_,rfl⟩
    · exact known
    · simp [store,put]
  exact (earlier.trans (force actual)).writer missing present

end MicroCFTA.SourceCurrentActualTargetSlotHistory

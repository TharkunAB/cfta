import MicroCFTA.SourceCurrentConjunctionSharedWorklistStep
import MicroCFTA.SourceCurrentConjunctionRequirementRowsFrame
import MicroCFTA.SourceCurrentConjunctionRequirementCellsFrame

/-!
# Actual private-handle validity in shared work

Every table row handle is within the spine heap. Every requirement handle
in a cached live row is within the cell heap. Initial allocation derives
both properties. Actual row preparation allocates the recorded requirement
handles before it publishes a row. All successful and failed transitions
preserve these bounds. Terminal materialization remains separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistHandleValidity
open InternedConstructorTemplates (Value EdgeKey EdgeValue)
open SourceCurrentConjunctionSharedWorklistStep
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "RowState" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Spine" => SourceCurrentConjunctionRequirementRows.Spine Symbol Formula

/-- Every requirement handle in a cached live row is within the actual cell heap. -/
def CellHandles (count : Nat) : Spine → Prop
  | .pending _ | .done none => True
  | .done (some (handles, _)) => ∀ handle ∈ handles, handle < count

/-- All cached row cells have valid requirement handles. -/
def RowCells (state : RowState) : Prop :=
  ∀ spine ∈ state.spines, CellHandles state.requirements.cells.length spine

/-- Every optional table row handle is within the actual spine heap. -/
def TableRows (state : WorkState) : Prop :=
  ∀ entry ∈ state.table, ∀ handle, entry.rows = some handle → handle < state.storage.spines.length

/-- The exact table and cached rows retain valid private handles. -/
structure Valid (state : WorkState) : Prop where
  rows : RowCells state.storage
  table : TableRows state

private theorem handles_mono (first last : Nat) (spine : Spine)
    (valid : CellHandles first spine) (grown : first ≤ last) : CellHandles last spine := by
  cases spine with
  | pending tuples => trivial
  | done row =>
      cases row with
      | none => trivial
      | some row =>
          intro handle member
          exact Nat.lt_of_lt_of_le (valid handle member) grown

private theorem rows_mono {before after : RowState} (valid : RowCells before)
    (same : after.spines = before.spines)
    (grown : before.requirements.cells.length ≤ after.requirements.cells.length) : RowCells after := by
  intro spine member
  rw [same] at member
  exact handles_mono _ _ spine (valid spine member) grown

private theorem rows_update (handle : Nat) (replacement : Spine) (before : RowState)
    (valid : RowCells before) (own : CellHandles before.requirements.cells.length replacement) :
    RowCells (SourceCurrentConjunctionRequirementRows.updateSpine handle replacement before) := by
  intro spine member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid spine old
  · exact same.symm ▸ own

private theorem rows_allocate (tuples : List (List Row)) (before : RowState) (valid : RowCells before) :
    RowCells (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending tuples) before).2 := by
  intro spine member
  rcases List.mem_append.mp member with old | fresh
  · exact valid spine old
  · have same : spine = .pending tuples := List.mem_singleton.mp fresh
    cases same
    trivial

private theorem allocated_handles (cells : List (SourceCurrentConjunctionRequirementCells.Cell Symbol Formula))
    (before : SourceCurrentConjunctionRequirementCells.State Symbol Formula) :
    ∀ handle ∈ (SourceCurrentConjunctionRequirementRows.allocateCells cells before).1,
      handle < (SourceCurrentConjunctionRequirementRows.allocateCells cells before).2.cells.length := by
  intro handle member
  rw [SourceCurrentConjunctionRequirementRows.allocateCells_handles] at member
  obtain ⟨index, inside, same⟩ := List.mem_range'.mp member
  rw [SourceCurrentConjunctionRequirementRows.allocateCells_order]
  simp only [List.length_append]
  simp only [Nat.one_mul] at same
  omega

private theorem prepared_handles (tuple : List Row) (before after : RowState) (handles : List Nat)
    (actual : SourceCurrentConjunctionRequirementRows.prepareTuple tuple before = .done (some handles) after) :
    ∀ handle ∈ handles, handle < after.requirements.cells.length := by
  unfold SourceCurrentConjunctionRequirementRows.prepareTuple at actual
  dsimp only at actual
  split at actual
  · cases actual
  · cases actual
  · split at actual
    · cases actual
    · cases actual
      exact allocated_handles _ _

private theorem prepared_rows (tuple : List Row) (before : RowState) (valid : RowCells before) :
    RowCells (SourceCurrentConjunctionRequirementRows.prepareTuple tuple before).state :=
  rows_mono valid (SourceCurrentConjunctionRequirementRows.prepareTuple_spines tuple before)
    (SourceCurrentConjunctionRequirementRowsFrame.prepareTuple_cells_le tuple before)

private theorem pending_rows (handle : Nat) (tuples : List (List Row)) (before : RowState)
    (valid : RowCells before)
    (found : SourceCurrentConjunctionRequirementRows.lookupSpine handle before = some (.pending tuples)) :
    RowCells (SourceCurrentConjunctionRequirementRows.nextRow handle before).state := by
  open SourceCurrentConjunctionRequirementRows in
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      exact rows_update handle (.done none) before valid True.intro
  | cons tuple rest ih =>
      have first := prepared_rows tuple before valid
      have retained := prepareTuple_spines tuple before
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          simpa only [prepared, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
      | done row after =>
          have kept : RowCells after := by
            simpa only [prepared, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
          rw [prepared] at retained
          change after.spines = before.spines at retained
          have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [retained]
            exact found
          cases row with
          | none =>
              rw [nextRow_rejected handle tuple rest before after found prepared]
              exact ih (updateSpine handle (.pending rest) after)
                (rows_update handle (.pending rest) after kept True.intro)
                (lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after afterFound)
          | some handles =>
              have own := prepared_handles tuple before after handles prepared
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact rows_update handle (.done (some (handles, after.spines.length)))
                (allocateSpine (.pending rest) after).2 (rows_allocate rest after kept) own

/-- Every actual row outcome preserves valid requirement handles in all cached rows. -/
theorem nextRow_valid (handle : Nat) (before : RowState) (valid : RowCells before) :
    RowCells (SourceCurrentConjunctionRequirementRows.nextRow handle before).state := by
  open SourceCurrentConjunctionRequirementRows in
  cases found : lookupSpine handle before with
  | none => rw [nextRow_missing handle before found]; exact valid
  | some spine =>
      cases spine with
      | done row => rw [nextRow_hit handle row before found]; exact valid
      | pending tuples => exact pending_rows handle tuples before valid found

private theorem storage_changed {before : WorkState} (valid : Valid before) (storage : RowState)
    (rows : RowCells storage) (grown : before.storage.spines.length ≤ storage.spines.length) :
    Valid {before with storage := storage} := by
  refine ⟨rows, ?_⟩
  intro entry member handle found
  exact Nat.lt_of_lt_of_le (valid.table entry member handle found) grown

/-- Actual source initialization derives table and cached-row handle validity. -/
theorem initial (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Valid (SourceCurrentConjunctionSharedWorklistStep.initial budget start before) := by
  constructor
  · intro spine member
    cases member
  · intro entry member
    cases member

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual visit derives valid table and cached-row handles, including sampling faults. -/
theorem visit_valid (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (valid : Valid before) : Valid (visit h nodes rest before).state := by
  unfold visit
  split
  · exact ⟨valid.rows, valid.table⟩
  · split
    · exact ⟨valid.rows, valid.table⟩
    · cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
          before.storage.requirements.physical with
      | failed fault physical => exact ⟨valid.rows, valid.table⟩
      | done result physical =>
          cases result with
          | overflow tuples cursor => exact ⟨valid.rows, valid.table⟩
          | fit tuples =>
              cases tuples with
              | nil =>
                  refine ⟨valid.rows, ?_⟩
                  intro entry member handle found
                  rcases List.mem_cons.mp member with same | old
                  · cases same
                    cases found
                  · exact valid.table entry old handle found
              | cons tuple tuples =>
                  change Valid
                    { budget := before.budget - (tuples.length + 1)
                      table := ⟨nodes, some before.storage.spines.length⟩ :: before.table
                      pending := .rows before.storage.spines.length :: rest
                      storage := (SourceCurrentConjunctionRequirementRows.allocateSpine
                        (.pending (tuple :: tuples)) (withPhysical before physical).storage).2 }
                  have exposed : RowCells (withPhysical before physical).storage := valid.rows
                  refine ⟨rows_allocate _ _ exposed, ?_⟩
                  intro entry member handle found
                  change entry ∈ ⟨nodes, some before.storage.spines.length⟩ :: before.table at member
                  change handle < (before.storage.spines ++
                    [SourceCurrentConjunctionRequirementRows.Spine.pending (tuple :: tuples)]).length
                  simp only [List.length_append, List.length_singleton]
                  rcases List.mem_cons.mp member with same | old
                  · cases same
                    have equal : before.storage.spines.length = handle := Option.some.inj found
                    omega
                  · have inside := valid.table entry old handle found
                    omega

/-- Every actual task outcome derives valid table and cached-row handles. -/
theorem step_valid (p h : Nat) (before : WorkState) (valid : Valid before) :
    Valid (step p h before).state := by
  cases pending : before.pending with
  | nil => rw [step_nil p h before pending]; exact valid
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_valid h nodes rest before valid
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact ⟨valid.rows, valid.table⟩
          | cons handle handles =>
              have length := SourceCurrentConjunctionRequirementCellsFrame.force_length
                p h handle before.storage.requirements
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle
                  before.storage.requirements with
              | failed fault cells =>
                  rw [forced] at length
                  change cells.cells.length = before.storage.requirements.cells.length at length
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact storage_changed valid _ (rows_mono valid.rows rfl (by
                    change before.storage.requirements.cells.length ≤ cells.cells.length
                    omega)) (Nat.le_refl _)
              | done nodes cells =>
                  rw [forced] at length
                  change cells.cells.length = before.storage.requirements.cells.length at length
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  apply visit_valid
                  exact storage_changed valid _ (rows_mono valid.rows rfl (by
                    change before.storage.requirements.cells.length ≤ cells.cells.length
                    omega)) (Nat.le_refl _)
      | rows handle =>
          have rows := nextRow_valid handle before.storage valid.rows
          have grown := SourceCurrentConjunctionRequirementRowsFrame.nextRow_spines_le handle before.storage
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [advanced] at rows grown
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact storage_changed valid storage rows grown
          | done row storage =>
              rw [advanced] at rows grown
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact ⟨rows, (storage_changed valid storage rows grown).table⟩
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact ⟨rows, (storage_changed valid storage rows grown).table⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistHandleValidity

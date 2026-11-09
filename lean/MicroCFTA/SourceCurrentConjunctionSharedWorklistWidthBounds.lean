import MicroCFTA.SourceCurrentConjunctionSharedWorklistStep
import MicroCFTA.SourceCurrentConjunctionRequirementCellsSize
import MicroCFTA.SourceCurrentConjunctionRequirementRowsNumericControl
import MicroCFTA.SourceCurrentConjunctionTuplePullShapes

/-!
# Current widths through actual shared transitions

Widths bound queued conjunctions, table queries and stored pending tuples.
Sampling keeps every operand position. Row forcing retains raw tuple widths.
A forced requirement returns at most the size of its actual initial cell.

Each step therefore uses the maximum of the old width and current cell size.
These laws include faults and need no semantic or future-state premises.
They do not bound the number or size of allocated requirement descriptors.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistWidthBounds
open InternedConstructorTemplates (Value EdgeKey EdgeValue)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionRequirementRowsNumericControl (RawWidths)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

/-- Every current query and pending raw tuple respects the same operand-count bound. -/
structure Widths (bound : Nat) (before : WorkState) : Prop where
  pending : ∀ nodes, Task.nodes nodes ∈ before.pending → nodes.length ≤ bound
  table : ∀ entry ∈ before.table, entry.nodes.length ≤ bound
  raw : RawWidths bound before.storage

/-- A larger bound retains the same current width facts. -/
theorem Widths.mono {bound larger : Nat} {before : WorkState} (prior : Widths bound before)
    (grown : bound ≤ larger) : Widths larger before := by
  refine ⟨fun nodes member => Nat.le_trans (prior.pending nodes member) grown,
    fun entry member => Nat.le_trans (prior.table entry member) grown, ?_⟩
  intro spine member
  have own := prior.raw spine member
  cases spine with
  | pending tuples =>
      intro tuple included
      exact Nat.le_trans (own tuple included) grown
  | done row => trivial

/-- Original initialization has one queued operand and empty table and row storage. -/
theorem initial_widths (budget : Nat) (start : Node) (before : Physical) :
    Widths 1 (SourceCurrentConjunctionSharedWorklistStep.initial budget start before) := by
  refine ⟨?_, ?_, ?_⟩
  · intro nodes member
    have same : nodes = [start] := Task.nodes.inj (List.mem_singleton.mp member)
    rw [same]
    exact Nat.le_refl _
  · intro entry member
    cases member
  · intro spine member
    cases member

private theorem bound_size (handle : Nat) (before : Cells) :
    SourceCurrentConjunctionRequirementCellsOutputBounds.bound handle before ≤
      SourceCurrentConjunctionRequirementCellsSize.stateSize before := by
  cases found : SourceCurrentConjunctionRequirementCells.lookup handle before with
  | none =>
      simp only [SourceCurrentConjunctionRequirementCellsOutputBounds.bound, found]
      exact Nat.zero_le _
  | some cell =>
      have sized := SourceCurrentConjunctionRequirementCellsSize.lookup_size handle before cell found
      cases cell with
      | column nodes =>
          simpa only [SourceCurrentConjunctionRequirementCellsOutputBounds.bound, found,
            SourceCurrentConjunctionRequirementCellsSize.size] using sized
      | done nodes =>
          simpa only [SourceCurrentConjunctionRequirementCellsOutputBounds.bound, found,
            SourceCurrentConjunctionRequirementCellsSize.size] using sized
      | pending cursor =>
          have inside : cursor.collected.length + cursor.pending.length ≤
              SourceCurrentConjunctionRequirementCellsSize.size (.pending cursor) :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          simpa only [SourceCurrentConjunctionRequirementCellsOutputBounds.bound, found] using
            Nat.le_trans inside sized

private theorem allocate_widths (bound : Nat) (tuples : List (List Row)) (before : Storage)
    (prior : RawWidths bound before) (own : ∀ tuple ∈ tuples, tuple.length ≤ bound) :
    RawWidths bound (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending tuples) before).2 := by
  intro spine member
  rcases List.mem_append.mp member with old | fresh
  · exact prior spine old
  · have same : spine = .pending tuples := List.mem_singleton.mp fresh
    cases same
    exact own

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
private theorem force_output_width {p h handle : Nat} {before after : Cells} {nodes : List Node}
    (actual : SourceCurrentConjunctionRequirementCells.force p h handle before = .done nodes after) :
    nodes.length ≤ SourceCurrentConjunctionRequirementCellsSize.stateSize before :=
  Nat.le_trans (SourceCurrentConjunctionRequirementCellsOutputBounds.force_length actual) (bound_size handle before)

/-- Every actual visit retains current query widths and derives the same width for each sampled tuple. -/
theorem visit_widths (bound h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (prior : Widths bound {before with pending := .nodes nodes :: rest}) :
    Widths bound (visit h nodes rest before).state := by
  have tail : ∀ query, Task.nodes query ∈ rest → query.length ≤ bound :=
    fun query member => prior.pending query (List.mem_cons_of_mem _ member)
  have own : nodes.length ≤ bound := prior.pending nodes List.mem_cons_self
  cases empty : nodes.any isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact ⟨tail, prior.table, prior.raw⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
          before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact ⟨tail, prior.table, prior.raw⟩
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact ⟨prior.pending, prior.table, prior.raw⟩
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact ⟨tail, prior.table, prior.raw⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      refine ⟨tail, ?_, prior.raw⟩
                      intro entry member
                      rcases List.mem_cons.mp member with rfl | old
                      · exact own
                      · exact prior.table entry old
                  | cons tuple tuples =>
                      have shapes := SourceCurrentConjunctionTuplePullShapes.sample_fit h before.budget nodes
                        before.storage.requirements.physical physical (tuple :: tuples) sampled
                      have raw : RawWidths bound (SourceCurrentConjunctionRequirementRows.allocateSpine
                          (.pending (tuple :: tuples)) (withPhysical before physical).storage).2 :=
                        allocate_widths bound (tuple :: tuples) (withPhysical before physical).storage prior.raw
                          (fun next member => Nat.le_trans (Nat.le_of_eq (shapes next member).1) own)
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      refine ⟨?_, ?_, raw⟩
                      · intro query member
                        rcases List.mem_cons.mp member with impossible | old
                        · cases impossible
                        · exact tail query old
                      · intro entry member
                        rcases List.mem_cons.mp member with rfl | old
                        · exact own
                        · exact prior.table entry old

/-- Every actual step bounds new conjunctions by the old width and the current cell size, including faults. -/
theorem step_widths (bound p h : Nat) (before : WorkState) (prior : Widths bound before) :
    Widths (max bound (SourceCurrentConjunctionRequirementCellsSize.stateSize before.storage.requirements))
      (step p h before).state := by
  let larger := max bound (SourceCurrentConjunctionRequirementCellsSize.stateSize before.storage.requirements)
  have old : Widths larger before := prior.mono (Nat.le_max_left _ _)
  change Widths larger (step p h before).state
  cases pending : before.pending with
  | nil => rw [step_nil p h before pending]; exact old
  | cons task rest =>
      have tail : ∀ query, Task.nodes query ∈ rest → query.length ≤ larger := by
        intro query member
        apply old.pending query
        rw [pending]
        exact List.mem_cons_of_mem _ member
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          apply visit_widths larger h nodes rest before
          refine ⟨?_, old.table, old.raw⟩
          intro query member
          apply old.pending query
          rw [pending]
          exact member
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact ⟨tail, old.table, old.raw⟩
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact ⟨old.pending, old.table, old.raw⟩
              | done nodes cells =>
                  have own : nodes.length ≤ larger :=
                    Nat.le_trans (force_output_width forced) (Nat.le_max_right _ _)
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  apply visit_widths larger h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                  refine ⟨?_, old.table, old.raw⟩
                  intro query member
                  rcases List.mem_cons.mp member with same | member
                  · have equal : query = nodes := Task.nodes.inj same
                    subst query
                    exact own
                  · rcases List.mem_cons.mp member with impossible | oldMember
                    · cases impossible
                    · exact tail query oldMember
      | rows handle =>
          have raw := SourceCurrentConjunctionRequirementRowsNumericControl.nextRow_widths larger handle before.storage old.raw
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              refine ⟨old.pending, old.table, ?_⟩
              simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state, Outcome.state] using raw
          | done row storage =>
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  refine ⟨tail, old.table, ?_⟩
                  simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state, Outcome.state] using raw
              | some row =>
                  rcases row with ⟨handles, next⟩
                  rw [step_rows_live p h handle next before rest handles storage pending advanced]
                  refine ⟨?_, old.table, ?_⟩
                  · intro query member
                    rcases List.mem_cons.mp member with impossible | member
                    · cases impossible
                    · rcases List.mem_cons.mp member with impossible | oldMember
                      · cases impossible
                      · exact tail query oldMember
                  · simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state, Outcome.state] using raw

end MicroCFTA.SourceCurrentConjunctionSharedWorklistWidthBounds

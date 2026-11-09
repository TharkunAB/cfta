import MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterialization
import MicroCFTA.SourceCurrentConjunctionSharedWorklistHandleValidity

/-!
# Complete pure reading of the cached shared table

Valid table handles and completed private cells let the existing reader
read every entry. The reader retains the literal query order. These local
cache premises must be derived from actual drained execution by the caller.
The reader performs no projection, equality fold, or further worker step.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistTableRead
open InternedConstructorTemplates (Value)
open SourceCurrentConjunctionSharedWorklistMaterialization
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "OldEntry" => SourceCurrentConjunctionEmptinessTable.Entry Node

private theorem mapM_complete (read : α → Option β) (inputs : List α)
    (complete : ∀ input ∈ inputs, ∃ output, read input = some output) :
    ∃ outputs, inputs.mapM read = some outputs := by
  induction inputs with
  | nil => exact ⟨[], rfl⟩
  | cons input rest ih =>
      obtain ⟨output, first⟩ := complete input List.mem_cons_self
      obtain ⟨outputs, last⟩ := ih (fun item member => complete item (List.mem_cons_of_mem _ member))
      refine ⟨output :: outputs, ?_⟩
      rw [List.mapM_cons]
      change (read input).bind (fun head => (rest.mapM read).bind
        (fun tail => some (head :: tail))) = some (output :: outputs)
      rw [first]
      change (rest.mapM read).bind (fun tail => some (output :: tail)) = some (output :: outputs)
      rw [last]
      rfl

private theorem mapM_projection (read : α → Option β) (source : α → γ) (target : β → γ)
    (preserved : ∀ input output, read input = some output → target output = source input)
    (inputs : List α) (outputs : List β) (actual : inputs.mapM read = some outputs) :
    outputs.map target = inputs.map source := by
  induction inputs generalizing outputs with
  | nil =>
      simp only [List.mapM_nil] at actual
      cases actual
      rfl
  | cons input rest ih =>
      rw [List.mapM_cons] at actual
      change (read input).bind (fun head => (rest.mapM read).bind
        (fun tail => some (head :: tail))) = some outputs at actual
      cases first : read input with
      | none => simp only [first, Option.bind_none] at actual; cases actual
      | some output =>
          cases last : rest.mapM read with
          | none => simp only [first, last, Option.bind_some, Option.bind_none] at actual; cases actual
          | some tail =>
              simp only [first, last, Option.bind_some] at actual
              cases actual
              simp only [List.map_cons, preserved input output first, ih tail last]

/-- Every table entry can be read from internally valid handles and completed cached rows. -/
theorem readTable_complete (credits : List Nat) (before : WorkState)
    (creditValid : SourceCurrentConjunctionRequirementRowsOrigins.Credits credits before.storage)
    (cellsCached : CellsCached before.storage) (spinesCached : SpinesCached before.storage)
    (valid : SourceCurrentConjunctionSharedWorklistHandleValidity.Valid before) :
    ∃ table, readTable credits before = some table := by
  unfold readTable
  apply mapM_complete
  intro entry member
  cases selected : entry.rows with
  | none =>
      refine ⟨⟨entry.nodes, []⟩, ?_⟩
      rfl
  | some handle =>
      obtain ⟨rows, read⟩ := readRows_complete credits handle before.storage creditValid
        cellsCached spinesCached valid.rows (valid.table entry member handle selected)
      refine ⟨⟨entry.nodes, rows⟩, ?_⟩
      change (readRows credits handle before.storage).bind
        (fun result => some (SourceCurrentConjunctionEmptinessTable.Entry.mk entry.nodes result)) = _
      rw [read]
      rfl

/-- Every successful read retains all queries in the identical table order. -/
theorem readTable_nodes (credits : List Nat) (before : WorkState)
    (table : SourceCurrentConjunctionWorker.Table Symbol Formula)
    (actual : readTable credits before = some table) :
    table.map (fun entry => entry.nodes) = before.table.map (fun entry => entry.nodes) := by
  unfold readTable at actual
  apply mapM_projection _
    (fun entry : SourceCurrentConjunctionSharedWorklistStep.Entry Symbol Formula => entry.nodes)
    (fun entry : OldEntry => entry.nodes) _
    before.table table actual
  intro entry output observed
  cases selected : entry.rows with
  | none =>
      simp only [selected] at observed
      cases observed
      rfl
  | some handle =>
      simp only [selected] at observed
      cases read : readRows credits handle before.storage with
      | none => simp only [read] at observed; cases observed
      | some rows =>
          simp only [read] at observed
          cases observed
          rfl

end MicroCFTA.SourceCurrentConjunctionSharedWorklistTableRead

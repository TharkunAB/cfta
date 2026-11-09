import MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationGraph

/-!
# Cached table reads do not depend on the chosen valid credits

Credits justify recursion through actual cached tails. They do not select
the returned rows. Any two valid certificates for the same storage give
the same optional result, including failed reads. Table reading also ignores
the worklist budget and pending tasks. No cache completion or execution
premise is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistReadExtensionality
open InternedConstructorTemplates (Value)
open SourceCurrentConjunctionRequirementRowsOrigins (Credits)
open SourceCurrentConjunctionSharedWorklistMaterialization (readRows readTable)
open SourceCurrentConjunctionSharedWorklistMaterializationGraph (RowsRead)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "SharedEntry" => SourceCurrentConjunctionSharedWorklistStep.Entry Symbol Formula
local notation "OldEntry" => SourceCurrentConjunctionEmptinessTable.Entry Node

private theorem recredit {first second : List Nat} {before : Storage} {handle : Nat}
    {rows : List (List (List Node))} (actual : RowsRead first before handle rows)
    (valid : Credits second before) : RowsRead second before handle rows := by
  induction actual with
  | nil _ cached =>
      obtain ⟨credit, own, _⟩ := valid.cells _ _ cached
      exact .nil own cached
  | cons _ cached head _ _ _ ih =>
      obtain ⟨credit, next, own, nextFound, smaller, _⟩ :=
        SourceCurrentConjunctionRequirementRowsOrigins.cached_tail valid _ _ _ cached
      exact .cons own cached head nextFound smaller ih

private theorem readRows_recredit (first second : List Nat) (handle : Nat) (before : Storage)
    (valid : Credits second before) (rows : List (List (List Node)))
    (actual : readRows first handle before = some rows) :
    readRows second handle before = some rows :=
  (recredit (SourceCurrentConjunctionSharedWorklistMaterializationGraph.readRows_graph
    first handle before rows actual) valid).replay

/-- Any two valid certificates give the identical optional cached row stream. -/
theorem readRows_credit_eq (first second : List Nat) (handle : Nat) (before : Storage)
    (firstValid : Credits first before) (secondValid : Credits second before) :
    readRows first handle before = readRows second handle before := by
  cases firstRead : readRows first handle before with
  | none =>
      cases secondRead : readRows second handle before with
      | none => rfl
      | some rows =>
          have same := readRows_recredit second first handle before firstValid rows secondRead
          rw [firstRead] at same
          cases same
  | some rows =>
      exact (readRows_recredit first second handle before secondValid rows firstRead).symm

/-- The exact table data and read failure do not depend on a chosen valid credit vector. -/
theorem readTable_credit_eq (first second : List Nat) (before : WorkState)
    (firstValid : Credits first before.storage) (secondValid : Credits second before.storage) :
    readTable first before = readTable second before := by
  unfold readTable
  have same : (fun entry : SharedEntry => do
        let rows ← match entry.rows with
          | none => some []
          | some handle => readRows first handle before.storage
        some (⟨entry.nodes, rows⟩ : OldEntry)) =
      (fun entry : SharedEntry => do
        let rows ← match entry.rows with
          | none => some []
          | some handle => readRows second handle before.storage
        some (⟨entry.nodes, rows⟩ : OldEntry)) := by
    funext entry
    dsimp only
    cases selected : entry.rows with
    | none => rfl
    | some handle =>
        change (readRows first handle before.storage).bind
            (fun rows => some (⟨entry.nodes, rows⟩ : OldEntry)) =
          (readRows second handle before.storage).bind
            (fun rows => some (⟨entry.nodes, rows⟩ : OldEntry))
        rw [readRows_credit_eq first second handle before.storage firstValid secondValid]
  exact congrArg (fun read : SharedEntry → Option OldEntry => before.table.mapM read) same

/-- Equal actual storage and table entries suffice even when other worklist fields differ. -/
theorem readTable_ext (first second : List Nat) (before after : WorkState)
    (firstValid : Credits first before.storage) (secondValid : Credits second after.storage)
    (storageSame : before.storage = after.storage) (tableSame : before.table = after.table) :
    readTable first before = readTable second after := by
  have valid : Credits first after.storage := storageSame ▸ firstValid
  calc
    readTable first before = readTable first after := by
      simp only [readTable, storageSame, tableSame]
    _ = readTable second after := readTable_credit_eq first second after valid secondValid

end MicroCFTA.SourceCurrentConjunctionSharedWorklistReadExtensionality

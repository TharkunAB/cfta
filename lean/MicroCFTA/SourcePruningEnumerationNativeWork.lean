import MicroCFTA.SourcePruningEnumerationStorageProgress
import MicroCFTA.EnumerationIndexSelection
import MicroCFTA.SourcePruningRecordTypes

/-!
# A finite scalar for native pending work

The scalar weights pending witness size and counts active candidates.
A recording callback preserves both fields at its actual successful result.
The initial witness bound and whole-cycle decrease remain separate obligations.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeWork
open Language EnumerationState EnumerationCorrectness EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type}

/-- Weight pending term size and the actual finite candidate list. -/
def work (initialBound : Nat) (before : Cached) (assignment : Nat → Term Symbol) : Nat :=
  (initialBound + 1) * pendingSize before.core assignment +
    (EnumerationIndexSelection.candidates before).length

/-- Every actual successful recording callback preserves the scalar. -/
theorem recordTypes_work
    (initialBound : Nat) (graph : Graph Symbol Constraint)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat) (before : Cached) (after : Core)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (assignment : Nat → Term Symbol) (total : UnionFind.Total before.core.representatives)
    (observed : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before.core result after) :
    work initialBound (EnumerationExpandableIndex.frame after before) assignment =
      work initialBound before assignment := by
  have framed := SourcePruningRecordTypes.recordTypes_frame graph templates fuel
    metadata uv input before.core after result total observed
  have cost : pendingSize after assignment = pendingSize before.core assignment := by
    unfold pendingSize
    rw [framed.values]
  unfold work
  change (initialBound + 1) * pendingSize after assignment +
    ((List.range after.counter).filter before.expandable).length = _
  rw [cost, framed.counter]
  rfl

end MicroCFTA.SourcePruningEnumerationNativeWork

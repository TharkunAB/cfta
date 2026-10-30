import MicroCFTA.SourcePruningEnumerationEnabledEmpty
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored

/-!
# Native cache certificates across the enabled emptiness worker

The actual physical result retains the caller's native tables.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredEnabledEmpty
open InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryStored
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Both actual conjunction outcomes retain the native structural certificates. -/
theorem call_stored (p h budget : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (stored : Stored before.native) :
    Stored (SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo).state.native := by
  unfold SourceCurrentAllocatedConjunctionWorker.call
  cases actual : SourceCurrentConjunctionWorker.call p h budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before) with
  | done result after =>
      rcases result with ⟨answer, saved⟩
      exact advance_stored before.native {before.native.machine with heap := after.heap} stored
  | failed fault after =>
      exact advance_stored before.native {before.native.machine with heap := after.heap} stored

/-- The actual endpoint query and enabled fourth-memo check retain native certificates. -/
theorem check_stored (p h : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (queries : Queries) (stored : Stored before.native) :
    Stored (SourcePruningEnumerationEnabledEmpty.check p h query before memo queries).1.state.native := by
  dsimp only [SourcePruningEnumerationEnabledEmpty.check]
  split
  · exact call_stored p h 1000 query before memo stored
  · exact stored

end MicroCFTA.SourceCurrentAllocatedNativeStoredEnabledEmpty

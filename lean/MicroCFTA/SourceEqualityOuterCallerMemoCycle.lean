import MicroCFTA.SourceEqualityOuterCallerCycle
import MicroCFTA.FlatMemoThunkRunning

/-!
# The checked outer caller cycle demands a running result thunk

The empty-inherited keys use the existing typed memo-thunk model.
Both strict child demands begin before either result can complete.
The repeated root lookup retains its original evaluating thunk.
Busy is a logical observation, not a specified GHC exception or result.
-/
namespace MicroCFTA.SourceEqualityOuterCallerMemoCycle
open InternedBinderProtocol

/-- The empty-inherited fiber uses physical node references as its remaining keys. -/
abbrev Memo := FlatMemoThunk.State NodeRef NodeRef NodeRef

/-- Start two distinct requests, then demand the original root through its published key. -/
def PendingCycle (root wrapper : NodeRef) : Prop :=
  let first := FlatMemoThunk.lookupOrInsert root root (FlatMemoThunk.empty : Memo)
  let runningRoot := FlatMemoThunk.demand first.1 first.2
  let second := FlatMemoThunk.lookupOrInsert wrapper wrapper runningRoot.2
  let runningWrapper := FlatMemoThunk.demand second.1 second.2
  let repeated := FlatMemoThunk.lookupOrInsert root root runningWrapper.2
  runningRoot.1 = .evaluate root ∧ runningWrapper.1 = .evaluate wrapper ∧
    repeated.1 = first.1 ∧ FlatMemoThunk.demand repeated.1 repeated.2 = (.busy, repeated.2) ∧
    FlatMemoThunk.completed repeated.2 root = none ∧ FlatMemoThunk.completed repeated.2 wrapper = none

/-- Publication and both actual demand phases retain the original unfinished root thunk. -/
theorem pending (root wrapper : NodeRef) (different : wrapper ≠ root) : PendingCycle root wrapper := by
  simp [PendingCycle, FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand,
    FlatMemoThunk.setStatus, FlatMemoThunk.completed, Cache.put, different, Ne.symm different]

/-- The kernel-checked source dependency cycle reaches busy with neither result completed. -/
theorem actual_pending : ∃ observed, SourceEqualityOuterCallerCycle.observation = some observed ∧
    observed.firstInherited = some [] ∧ observed.secondInherited = some [] ∧
    observed.returned = observed.original ∧ PendingCycle observed.original observed.wrapper := by
  obtain ⟨observed, found, same, first, second, different⟩ := SourceEqualityOuterCallerCycle.cycle
  exact ⟨observed, found, first, second, same, pending _ _ different⟩

end MicroCFTA.SourceEqualityOuterCallerMemoCycle

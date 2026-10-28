import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
import MicroCFTA.SourcePruningEnumerationIncomingNodeStability
import MicroCFTA.SourcePruningEnumerationNativeIndexStability

/-!
# Successful incoming cache observations at larger work bounds

An actual attached cache fixes the successful native indexed write.
The same raw incoming row retains the caller, query and outer read state.
The larger indexed write retains the entire original attached cache.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}

/-- An actual successful adapter retains its entire returned cache at every larger index bound. -/
theorem adapt_some_stable
    {heap : InternedConstructorTemplates.State Symbol Constraint} {k K target : Nat}
    {incomingScs : List Suspended} {before after : Cached} {read : Core} {raw : Raw}
    (observed : adapt heap k target incomingScs before read raw = some after)
    (enoughK : k ≤ K) : adapt heap K target incomingScs before read raw = some after := by
  have writeAt (value : UVarValue Symbol) (written : Cached)
      (actual : SourcePruningEnumerationNativeIndex.write heap k target value incomingScs []
        (EnumerationExpandableIndex.frame read before) = some written) :
      SourcePruningEnumerationNativeIndex.write heap K target value incomingScs []
        (EnumerationExpandableIndex.frame read before) = some written := by
    simpa only [Nat.add_sub_of_le enoughK] using
      SourcePruningEnumerationNativeIndex.write_some_moreFuel heap k (K - k) target value incomingScs []
        (EnumerationExpandableIndex.frame read before) written actual
  cases raw with
  | nil =>
      cases stored : read.values[target]? with
      | none => simp only [adapt, stored] at observed; cases observed
      | some value =>
          cases value with
          | eliminated | enumerated => simp only [adapt, stored] at observed; cases observed
          | unenumerated oldNode oldScs =>
              simp only [adapt, stored] at observed ⊢
              obtain ⟨written, actual, same⟩ := Option.map_eq_some_iff.mp observed
              exact Option.map_eq_some_iff.mpr ⟨written, writeAt _ written actual, same⟩
  | cons first rest =>
      cases first with
      | error fault => simp only [adapt] at observed; cases observed
      | ok row =>
          rcases row with ⟨token, returned⟩
          cases token
          cases rest with
          | cons next tail => simp only [adapt] at observed; cases observed
          | nil =>
              simp only [adapt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
              obtain ⟨value, stored, written, actual, same⟩ := observed
              simp only [adapt, stored, Option.bind_some]
              exact Option.map_eq_some_iff.mpr ⟨written, writeAt value written actual, same⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual successful row and attached cache retain every endpoint at larger work bounds. -/
theorem run_some_stable
    {checkEmpty : Bool} {r n p h k R N P H K : Nat}
    {caller reached : Caller width} {before after : Cached} {read : Core}
    {target : Nat} {incoming : Node} {incomingScs : List Suspended} {queries saved : Queries} {raw : Raw}
    (observed : run checkEmpty r n p h k caller before target incoming incomingScs queries =
      ((.ok (some raw), reached, saved, read), some after))
    (successful : raw = [] ∨ ∃ returned : Core, raw = [.ok ((), returned)])
    (enoughR : r ≤ R) (enoughN : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughK : k ≤ K) :
    run checkEmpty R N P H K caller before target incoming incomingScs queries =
      ((.ok (some raw), reached, saved, read), some after) := by
  have original : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h caller before.core
      target incoming incomingScs queries = (.ok (some raw), reached, saved, read) := by
    simpa only [run] using congrArg Prod.fst observed
  have larger := SourcePruningEnumerationIncomingNode.run_ok_stable
    original successful enoughR enoughN enoughP enoughH
  have adapted : adapt reached.checked.native.machine.heap k target incomingScs before read raw = some after := by
    simpa only [run, original] using congrArg Prod.snd observed
  simp only [run, larger, adapt_some_stable adapted enoughK]

end MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

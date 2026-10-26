import MicroCFTA.SourcePruningEnumerationNonterminalScalarBounds
import MicroCFTA.SourcePruningEnumerationTerminalCacheBounds

/-!
# Original scalar bounds for actual child caches

Every child adds at most one slot and its original incoming bucket length.
The bounds apply to the actual attached cache, including valid rejection.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual child cache growth is bounded by its original counter and bucket length. -/
theorem observed_scalar_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) (after : Cached)
    (observed : (run checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    after.core.counter ≤ before.core.counter + 1 ∧
      suspendedBound after.core ≤ suspendedBound before.core + scs.length := by
  by_cases empty : incoming = .empty
  · simp only [run, ite_eq_left empty, Option.some.injEq] at observed
    subst after
    exact ⟨Nat.le_succ _, Nat.le_add_right _ _⟩
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        simp only [run, ite_eq_right empty, partitioned] at observed
        cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild
            caller.checked.native.machine.heap k scs incoming before with
        | none => simp only [prepared] at observed; cases observed
        | some rows =>
          cases rows with
          | nil =>
            simp only [prepared, Option.some.injEq] at observed
            subst after
            exact ⟨Nat.le_succ _, Nat.le_add_right _ _⟩
          | cons row rest =>
            rcases row with ⟨fragment, returned⟩
            cases rest with
            | cons second remaining => simp only [prepared] at observed; cases observed
            | nil =>
              simp only [prepared, Option.some.injEq] at observed
              subst after
              have bounds := SourcePruningEnumerationCachedPrepare.singleton_counter_mass_bound
                caller.checked.native.machine.heap k scs incoming before returned fragment prepared
              exact ⟨Nat.le_of_eq bounds.1, bounds.2⟩
      | cons first rest =>
        have bounds := SourcePruningEnumerationCachedTerminalAdapter.observed_cache_bounds
          checkEmpty r n p h k first rest caller before incoming descendants queries after
          (by simpa only [run, ite_eq_right empty, partitioned] using observed)
        have partitionSecond := congrArg Prod.snd partitioned
        simp only [List.partition_eq_filter_filter] at partitionSecond
        have descendantsBound : descendants.length ≤ scs.length := by
          rw [← partitionSecond]
          exact List.length_filter_le _ _
        exact ⟨by rw [bounds.1]; exact Nat.le_succ _,
          Nat.le_trans bounds.2 (Nat.add_le_add_left descendantsBound _)⟩

end MicroCFTA.SourcePruningEnumerationChildDispatch

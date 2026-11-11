import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationSharedTerminalProper
import MicroCFTA.SourcePruningEnumerationCachedPrepareProper

/-!
# Proper paths at every attached shared child cache

The common nonterminal preparation retains proper stored paths.
The literal terminal partition supplies strict incoming descendants.
Rejected candidates retain proper paths without a safety claim.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationState EnumerationCorrectness EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual attached child candidate retains proper paths, including rejection. -/
theorem observed_cache_proper
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (proper : ProperState before.core) (inputs : ProperInputs scs) (after : Cached)
    (candidate : (run checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    ProperState after.core := by
  by_cases empty : incoming = .empty
  · simp only [run, empty, ↓reduceIte, Option.some.injEq] at candidate
    subst after
    exact proper
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        apply SourcePruningEnumerationCachedPrepare.cache_proper
          caller.checked.native.machine.heap k scs incoming before after proper inputs
        simp only [run, ite_eq_right empty, partitioned] at candidate
        cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild
            caller.checked.native.machine.heap k scs incoming before with
        | none => simpa only [prepared] using candidate
        | some rows =>
          cases rows with
          | nil => simpa only [prepared] using candidate
          | cons row tail =>
            rcases row with ⟨fragment, reached⟩
            cases tail with
            | nil => simpa only [prepared] using candidate
            | cons next rest => simpa only [prepared] using candidate
      | cons first rest =>
        apply SourcePruningEnumerationSharedCachedTerminal.candidate_partition_proper
          checkEmpty r n p h k scs first rest descendants caller before incoming queries
          proper inputs partitioned after
        simpa only [run, ite_eq_right empty, partitioned] using candidate

/-- A literal successful singleton supplies the same attached cache invariant. -/
theorem successful_proper
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {caller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (proper : ProperState before.core) (inputs : ProperInputs scs)
    (observed : run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    ProperState after.core :=
  observed_cache_proper checkEmpty r n p h k scs incoming caller before queries proper inputs after
    (congrArg Prod.snd observed)

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch

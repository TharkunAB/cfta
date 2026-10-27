import MicroCFTA.SourcePruningEnumerationTerminalProper
import MicroCFTA.SourcePruningEnumerationCachedPrepareProper
import MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates
import MicroCFTA.SourcePruningEnumerationChildTraversal

/-!
# Proper pending paths at actual child caches

The actual partition removes terminal tries before an incoming write.
Every attached cache retains proper paths, including rejected caches.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
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

/-- The actual child candidate retains proper paths on successful and rejected branches. -/
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
        simpa only [run, ite_eq_right empty, partitioned] using candidate
      | cons first rest =>
        have descendantsSame : scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie) = descendants := by
          simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
        have descendantsProper : ∀ sc ∈ descendants, ProperTrie sc.trie := by
          intro sc member
          apply proper_below scs inputs sc
          simpa only [descendantsSame] using member
        apply SourcePruningEnumerationCachedTerminalAdapter.candidate_proper checkEmpty r n p h k
          first rest caller before incoming descendants queries proper descendantsProper after
        simpa only [run, ite_eq_right empty, partitioned] using candidate

/-- An actual successful child derives proper paths at its exact attached cache. -/
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

end MicroCFTA.SourcePruningEnumerationChildDispatch

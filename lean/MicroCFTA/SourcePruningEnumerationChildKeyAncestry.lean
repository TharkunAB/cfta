import MicroCFTA.SourcePruningEnumerationTerminalKeyAncestry
import MicroCFTA.SourcePruningEnumerationCachedPrepareKeyAncestry
import MicroCFTA.SourcePruningEnumerationChildDispatch

/-!
# Historical key shapes at actual child cache candidates

Empty rejection returns the original cache.
Ordinary preparation, opaque allocation and the terminal path retain the carrier.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
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

/-- Every actual attached child cache retains the original historical key carrier. -/
theorem observed_cache_key_ancestry
    {carrier : List (List (List (List Nat)))}
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (bounded : KeyAncestry carrier before.core) (after : Cached)
    (candidate : (run checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    KeyAncestry carrier after.core := by
  by_cases empty : incoming = .empty
  · simp only [run, empty, ↓reduceIte, Option.some.injEq] at candidate
    subst after
    exact bounded
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        apply SourcePruningEnumerationCachedPrepare.cache_key_ancestry
          caller.checked.native.machine.heap k scs incoming before after bounded
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
        apply SourcePruningEnumerationCachedTerminalAdapter.candidate_key_ancestry checkEmpty r n p h k
          first rest caller before incoming descendants queries bounded after
        simpa only [run, ite_eq_right empty, partitioned] using candidate

/-- The exact successful child cache retains the original historical key carrier. -/
theorem successful_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {caller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (bounded : KeyAncestry carrier before.core)
    (observed : run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    KeyAncestry carrier after.core :=
  observed_cache_key_ancestry checkEmpty r n p h k scs incoming caller before queries bounded after
    (congrArg Prod.snd observed)

end MicroCFTA.SourcePruningEnumerationChildDispatch

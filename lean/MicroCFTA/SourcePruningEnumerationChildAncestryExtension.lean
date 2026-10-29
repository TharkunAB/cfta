import MicroCFTA.SourcePruningEnumerationTerminalAncestryExtension
import MicroCFTA.SourcePruningEnumerationAncestryExtensionOwn
import MicroCFTA.SourcePruningEnumerationChildDispatch

/-!
# Retained histories at actual child cache candidates

Empty rejection returns the original cache.
Ordinary preparation, opaque allocation and the terminal path retain every slot key.
Each exposed child cache keeps the original active expansion history.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
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

/-- Every actual attached child cache retains all slot keys and the expansion history. -/
theorem observed_cache_ancestry_extension
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (after : Cached)
    (candidate : (run checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  by_cases empty : incoming = .empty
  · simp only [run, empty, ↓reduceIte, Option.some.injEq] at candidate
    subst after
    exact ⟨Extends.refl before.core, rfl⟩
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        apply SourcePruningEnumerationCachedPrepare.cache_ancestry_extension
          caller.checked.native.machine.heap k scs incoming before after
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
        apply SourcePruningEnumerationCachedTerminalAdapter.candidate_ancestry_extension checkEmpty r n p h k
          first rest caller before incoming descendants queries after
        simpa only [run, ite_eq_right empty, partitioned] using candidate

/-- The exact successful child cache retains all slot keys and the expansion history. -/
theorem successful_ancestry_extension
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {caller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (observed : run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry :=
  observed_cache_ancestry_extension checkEmpty r n p h k scs incoming caller before queries after
    (congrArg Prod.snd observed)

end MicroCFTA.SourcePruningEnumerationChildDispatch

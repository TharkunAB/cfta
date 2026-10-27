import MicroCFTA.SourcePruningEnumerationTerminalCanonical
import MicroCFTA.SourcePruningEnumerationCachedPrepareCanonical
import MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates
import MicroCFTA.SourcePruningEnumerationChildTraversal

/-!
# Canonical stored tries through actual successful child dispatch

The actual partition retains valid inherited tries.
Successful raw rows and their attached caches have the same core.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
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

/-- Every actual successful child row derives canonicality of its exact attached cache. -/
theorem successful_canonical
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {caller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (canonical : Canonical before.core) (inputs : ValidSuspended scs)
    (observed : run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    Canonical after.core := by
  have coreSame := singleton_core checkEmpty r n p h k scs incoming caller reachedCaller before after
    queries savedQueries fragment returned outer waiting observed
  rw [coreSame]
  have original := (erase checkEmpty r n p h k scs incoming caller before queries).symm.trans
    (congrArg Prod.fst observed)
  by_cases empty : incoming = .empty
  · simp only [observe, empty, ↓reduceIte] at original
    cases original
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        simp only [observe, empty, ↓reduceIte, partitioned] at original
        cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
        | none => simp only [prepared] at original; cases original
        | some action =>
          rw [prepared] at original
          have rawSame := congrArg Prod.fst original
          dsimp only at rawSame
          have success : Success action before.core fragment returned := by
            rw [Success, Option.some.inj (Except.ok.inj rawSame)]
            exact List.mem_singleton_self _
          exact SourcePruningEnumerationShallowChild.prepared_canonical scs incoming before.core returned
            action fragment canonical inputs prepared success
      | cons first rest =>
        have validParts := (SourcePruningEnumerationOrdinarySemanticGates.partition_descendants scs
          (first :: rest) descendants partitioned).2 inputs
        apply SourcePruningEnumerationTerminal.successful_canonical checkEmpty r n p h first rest before.waiting
          caller before.core incoming descendants queries fragment reachedCaller savedQueries outer returned
          waiting canonical validParts.2
        simpa only [observe, empty, ↓reduceIte, partitioned] using original

end MicroCFTA.SourcePruningEnumerationChildDispatch

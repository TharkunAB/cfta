import MicroCFTA.SourcePruningEnumerationPreparedTerminalIsolation
import MicroCFTA.SourcePruningEnumerationChildEffects
import MicroCFTA.SourcePruningEnumerationCachedPrepareCanonical
import MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates
import MicroCFTA.SourcePruningEnumerationChildTraversal

/-!
# Original isolation through actual successful child dispatch

The actual partition retains exclusion of the original isolated class.
Successful raw rows and their attached caches have the same core.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationReferences EnumerationDischargeHistory
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

/-- Every actual successful child row retains the original isolated class outside its input bucket. -/
theorem successful_isolated
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {caller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (held heldHandle : Nat) (safe : Safe before.core)
    (isolated : IsolatedPending held heldHandle before.core)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (inputs : Avoids before.core.representatives held scs)
    (observed : run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    IsolatedPending held heldHandle after.core := by
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
          have inside : held < before.core.counter := by
            rw [safe.1.aligned]
            exact (List.getElem?_eq_some_iff.mp isolated.stored).1
          have preserved := (SourcePruningEnumerationChildEffects.child scs incoming action before.core returned
            fragment safe bounded prepared success).2.2 held inside isolated.root
          exact isolated.through_protected preserved scs inputs
            (fun allowed valid allowedInputs => SourcePruningEnumerationNativeReferences.prepared_allowed
              allowed scs incoming action before.core returned fragment valid allowedInputs prepared success)
      | cons first rest =>
        have activeMembers : (first :: rest) ⊆ scs := by
          intro sc member
          have retained : sc ∈ scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) := by
            simpa only [List.partition_eq_filter_filter] using
              (show sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 by
                simpa only [partitioned] using member)
          exact (List.mem_filter.mp retained).1
        have descendantMembers : descendants ⊆ scs := by
          intro sc member
          have retained : sc ∈ scs.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) := by
            simpa only [List.partition_eq_filter_filter, Function.comp_def] using
              (show sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).2 by
                simpa only [partitioned] using member)
          exact (List.mem_filter.mp retained).1
        apply SourcePruningEnumerationTerminal.successful_isolated checkEmpty r n p h first rest before.waiting
          caller before.core incoming descendants queries fragment reachedCaller savedQueries outer returned
          waiting held heldHandle safe.1.total isolated
          (fun sc member => inputs sc (activeMembers member))
          (fun sc member => inputs sc (descendantMembers member))
        simpa only [observe, empty, ↓reduceIte, partitioned] using original

end MicroCFTA.SourcePruningEnumerationChildDispatch

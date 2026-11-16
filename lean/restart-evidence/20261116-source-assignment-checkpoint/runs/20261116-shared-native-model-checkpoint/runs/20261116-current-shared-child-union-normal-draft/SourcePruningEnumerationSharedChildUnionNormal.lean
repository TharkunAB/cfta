import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal
open EnumerationState InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual child observation retains normality at its returned caller. -/
theorem observe_unionNormal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe
        checkEmpty representativeFuel nativeFuel p h scs incoming beforeCaller before waiting queries).2.1.checked.native.machine.heap := by
  unfold SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe
  by_cases empty : incoming = .empty
  · simpa only [ite_eq_left empty] using normal
  · simp only [ite_eq_right empty]
    cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        cases here with
        | nil =>
            cases SourcePruningEnumerationShallowChild.prepareChild scs incoming <;> exact normal
        | cons first rest =>
            exact SourcePruningEnumerationSharedCachedTerminalUnionNormal.raw_unionNormal
              checkEmpty representativeFuel nativeFuel p h first rest waiting beforeCaller before
              incoming descendants queries normal

/-- The cached child dispatcher retains the exact raw returned caller normality. -/
theorem run_unionNormal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
        checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming beforeCaller before queries).1.2.1.checked.native.machine.heap := by
  rw [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.erase]
  exact observe_unionNormal checkEmpty representativeFuel nativeFuel p h scs incoming
    beforeCaller before.core before.waiting queries normal

/-- Every actual ordered child traversal retains its complete or stopping caller normality. -/
theorem traversal_unionNormal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (inputs : List (Node × List Suspended))
    (beforeCaller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    match SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run
        checkEmpty representativeFuel nativeFuel p h indexFuel inputs beforeCaller before queries with
    | .complete _ afterCaller _ _ => UnionNormal afterCaller.checked.native.machine.heap
    | .stopped _ observation _ => UnionNormal observation.2.1.checked.native.machine.heap := by
  induction inputs generalizing beforeCaller before queries with
  | nil => exact normal
  | cons input rest ih =>
      obtain ⟨value, bucket⟩ := input
      have headNormal := run_unionNormal checkEmpty representativeFuel nativeFuel p h indexFuel
        bucket value beforeCaller before queries normal
      unfold SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run
      generalize dispatchObserved : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
        checkEmpty representativeFuel nativeFuel p h indexFuel bucket value beforeCaller before queries = actual
        at headNormal ⊢
      obtain ⟨⟨result, reachedCaller, savedQueries, outer, moved⟩, candidate⟩ := actual
      dsimp only at headNormal ⊢
      cases result with
      | error fault => exact headNormal
      | ok returned =>
          cases returned with
          | none => exact headNormal
          | some rows =>
              cases rows with
              | nil => exact headNormal
              | cons row tail =>
                  cases row with
                  | error rowError => exact headNormal
                  | ok rowValue =>
                      obtain ⟨fragment, returned⟩ := rowValue
                      cases tail with
                      | cons second remaining => exact headNormal
                      | nil =>
                          cases candidate with
                          | none => exact headNormal
                          | some after =>
                              have later := ih reachedCaller after savedQueries headNormal
                              cases tailObserved : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run
                                  checkEmpty representativeFuel nativeFuel p h indexFuel rest
                                  reachedCaller after savedQueries with
                              | complete fragments finalCaller finalQueries finalCache =>
                                  simpa only [tailObserved] using later
                              | stopped completedPrefix observation retainedCache =>
                                  simpa only [tailObserved] using later

end MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal

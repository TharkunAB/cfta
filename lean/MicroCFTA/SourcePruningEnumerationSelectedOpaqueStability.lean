import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildDispatchStability
import MicroCFTA.SourcePruningEnumerationNativeIndexStability

/-!
# Stable successful selected opaque dispatch

A literal completed point retains its fragment, caller, query memo and full cache.
Each work bound can increase independently.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual completed selected opaque point is identical at larger work bounds. -/
theorem complete_stable
    {checkEmpty : Bool} {r R n N p P h H k K target : Nat} {scs : List Suspended} {value : Node}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries} {fragment : Fragment}
    (completed : run checkEmpty r n p h k target scs value caller before queries =
      some (.complete fragment reached saved after))
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    run checkEmpty R N P H K target scs value caller before queries =
      some (.complete fragment reached saved after) := by
  have finalize (produced : Fragment) (childCaller : Caller width) (childQueries : Queries)
      (middle : Cached)
      (observed : (SourcePruningEnumerationFinalize.run childCaller.checked.native.machine.heap k target produced middle).map
        (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete produced childCaller childQueries finished) =
          some (.complete fragment reached saved after)) :
      (SourcePruningEnumerationFinalize.run childCaller.checked.native.machine.heap K target produced middle).map
        (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete produced childCaller childQueries finished) =
          some (.complete fragment reached saved after) := by
    obtain ⟨finished, finishRun, fields⟩ := Option.map_eq_some_iff.mp observed
    have finishLater := SourcePruningEnumerationFinalize.run_some_moreFuel
      childCaller.checked.native.machine.heap k (K - k) target produced middle finished finishRun
    have sameFuel : k + (K - k) = K := by omega
    rw [sameFuel] at finishLater
    simpa only [finishLater, Option.map_some, Option.some.injEq] using fields
  cases value with
  | empty =>
      simp only [run, ↓reduceIte, Option.some.injEq, reduceCtorEq] at completed
  | reference | mu | union =>
      simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at completed ⊢
      split at completed
      next produced returned childCaller childQueries outer waiting middle childRun =>
        have childLater := SourcePruningEnumerationChildDispatch.run_singleton_stable
          childRun enoughRepresentative enoughNative enoughP enoughH enoughIndex
        rw [childLater]
        exact finalize produced childCaller childQueries middle completed
      next => cases completed
  | node entry edges depth free =>
      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
      | true =>
          simp only [run, reduceCtorEq, terminal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at completed ⊢
          split at completed
          next produced returned childCaller childQueries outer waiting middle childRun =>
            have childLater := SourcePruningEnumerationChildDispatch.run_singleton_stable
              childRun enoughRepresentative enoughNative enoughP enoughH enoughIndex
            rw [childLater]
            exact finalize produced childCaller childQueries middle completed
          next => cases completed
      | false =>
          rw [ordinary_deferred checkEmpty r n p h k target scs entry edges depth free
            caller before queries terminal] at completed
          cases completed

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch

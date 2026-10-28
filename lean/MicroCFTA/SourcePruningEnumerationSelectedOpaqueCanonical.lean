import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildCanonical
import MicroCFTA.SourcePruningEnumerationOwnFinalizeCanonical

/-!
# Canonical storage through actual prepared opaque dispatch

The actual successful child row supplies its exact attached cache.
The captured-target finalizer preserves canonical stored suspended tries.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual completed opaque or terminal dispatch preserves canonical storage. -/
theorem complete_canonical
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {value : Node}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries} {fragment : Fragment}
    (canonical : Canonical before.core) (inputs : ValidSuspended scs)
    (completed : run checkEmpty r n p h k target scs value caller before queries =
      some (.complete fragment reached saved after)) : Canonical after.core := by
  have finalize (produced : Fragment) (returned outer : EnumerationState.State Symbol Constraint)
      (childCaller : Caller width) (childQueries : Queries) (waiting : EnumerationWaitingIndex.Waiting)
      (middle : Cached)
      (childRun : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs value caller before queries =
        ((.ok (some [.ok (produced, returned)]), childCaller, childQueries, outer, waiting), some middle))
      (observed : (SourcePruningEnumerationFinalize.run childCaller.checked.native.machine.heap k target produced middle).map
        (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete produced childCaller childQueries finished) =
          some (.complete fragment reached saved after)) : Canonical after.core := by
    obtain ⟨finished, finishRun, fields⟩ := Option.map_eq_some_iff.mp observed
    have cacheSame : finished = after :=
      (SourcePruningEnumerationSelectedEdge.Result.complete.inj fields).2.2.2
    rw [← cacheSame]
    exact SourcePruningEnumerationFinalize.run_canonical
      childCaller.checked.native.machine.heap k target produced middle finished
      (SourcePruningEnumerationChildDispatch.successful_canonical canonical inputs childRun) finishRun
  cases value with
  | empty =>
      simp only [run, ↓reduceIte, Option.some.injEq, reduceCtorEq] at completed
  | reference | mu | union =>
      simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at completed
      split at completed
      next produced returned childCaller childQueries outer waiting middle childRun =>
        exact finalize produced returned outer childCaller childQueries waiting middle childRun completed
      next => cases completed
  | node entry edges depth free =>
      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
      | true =>
          simp only [run, reduceCtorEq, terminal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at completed
          split at completed
          next produced returned childCaller childQueries outer waiting middle childRun =>
            exact finalize produced returned outer childCaller childQueries waiting middle childRun completed
          next => cases completed
      | false =>
          rw [ordinary_deferred checkEmpty r n p h k target scs entry edges depth free
            caller before queries terminal] at completed
          cases completed

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch

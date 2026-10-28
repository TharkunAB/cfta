import MicroCFTA.SourcePruningEnumerationPreparedChildIsolation
import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation

/-!
# Original isolation through an actual selected opaque receipt

The same actual child observation retains the original isolated class.
The finalizer writes a different selected target.
The proof includes terminal buckets and nonterminal opaque values.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDischargeHistory
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- One actual completed opaque dispatch retains a different original isolated root. -/
theorem completed_isolated
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries) (fragment : Fragment)
    (held heldHandle : Nat) (safe : Safe before.core)
    (isolated : IsolatedPending held heldHandle before.core)
    (different : target ≠ held)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (inputs : Avoids before.core.representatives held scs)
    (observed : run checkEmpty r n p h k target scs value caller before queries =
      some (.complete fragment reached saved after)) :
    IsolatedPending held heldHandle after.core := by
  have finalize (produced : Fragment) (returned outer : EnumerationState.State Symbol Constraint)
      (childCaller : Caller width) (childQueries : Queries) (waiting : EnumerationWaitingIndex.Waiting)
      (middle : Cached)
      (childRun : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs value caller before queries =
        ((.ok (some [.ok (produced, returned)]), childCaller, childQueries, outer, waiting), some middle))
      (finishObserved : (SourcePruningEnumerationFinalize.run childCaller.checked.native.machine.heap k target produced middle).map
        (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete produced childCaller childQueries finished) =
          some (.complete fragment reached saved after)) : IsolatedPending held heldHandle after.core := by
    obtain ⟨finished, finishRun, fields⟩ := Option.map_eq_some_iff.mp finishObserved
    have cacheSame : finished = after :=
      (SourcePruningEnumerationSelectedEdge.Result.complete.inj fields).2.2.2
    rw [← cacheSame]
    have childIsolated := SourcePruningEnumerationChildDispatch.successful_isolated held heldHandle
      safe isolated bounded inputs childRun
    exact childIsolated.through_finalize childCaller.checked.native.machine.heap k target held heldHandle
      produced middle finished different finishRun
  cases value with
  | empty =>
      simp only [run, ↓reduceIte, Option.some.injEq, reduceCtorEq] at observed
  | reference | mu | union =>
      simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at observed
      split at observed
      next produced returned childCaller childQueries outer waiting middle childRun =>
        exact finalize produced returned outer childCaller childQueries waiting middle childRun observed
      next => cases observed
  | node entry edges depth free =>
      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
      | true =>
          simp only [run, reduceCtorEq, terminal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at observed
          split at observed
          next produced returned childCaller childQueries outer waiting middle childRun =>
            exact finalize produced returned outer childCaller childQueries waiting middle childRun observed
          next => cases observed
      | false =>
          rw [ordinary_deferred checkEmpty r n p h k target scs entry edges depth free
            caller before queries terminal] at observed
          cases observed

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch

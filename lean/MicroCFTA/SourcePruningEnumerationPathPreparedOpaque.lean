import MicroCFTA.SourcePruningEnumerationPathHead
import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch

/-!
# Stored paths through actual Prepared opaque receipts

Complete and rejected receipts retain their returned cache paths. Stopped receipts retain both their actual
outer core paths and every actual candidate cache's paths. This property does
not assert native Context at a low-fuel fault heap.
-/
namespace MicroCFTA.SourcePruningEnumerationPathPreparedOpaque
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Every stored core retained in the selected opaque receipt satisfies the same predicate. -/
def ReceiptPaths (P : EqualityTrie.Path → Prop) : SourcePruningEnumerationSelectedEdge.Result width → Prop
  | .unhandled => True
  | .complete _ _ _ after => StatePaths P after.core
  | .rejected _ _ before => StatePaths P before.core
  | .stopped _ observation candidate =>
      StatePaths P observation.2.2.2.1 ∧
        ∀ after, candidate = some after → StatePaths P after.core

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual opaque observation retains paths before any continuation or output test. -/
theorem run_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs) :
    match SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs incoming caller before queries with
    | none => True
    | some receipt => ReceiptPaths P receipt := by
  generalize actual : SourcePruningEnumerationSelectedOpaqueDispatch.run
    checkEmpty r n p h k target scs incoming caller before queries = observed
  cases observed with
  | none => trivial
  | some receipt =>
      cases incomingEq : incoming <;>
        cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
        simp only [SourcePruningEnumerationSelectedOpaqueDispatch.run, incomingEq,
          reduceCtorEq, terminal, Bool.not_true, Bool.not_false, Bool.false_eq_true,
          ↓reduceIte] at actual
      all_goals
        first
        | have same := Option.some.inj actual
          cases same
          exact paths
        | rw [← incomingEq] at actual
          generalize childEq : SourcePruningEnumerationChildDispatch.run
            checkEmpty r n p h k scs incoming caller before queries = child at actual
          rcases child with ⟨observation, candidate⟩
          rcases observation with ⟨raw, reached, saved, outer, waiting⟩
          have outerPaths : StatePaths P outer := by
            simpa only [childEq] using SourcePruningEnumerationChildDispatch.run_outer_paths
              checkEmpty r n p h k scs incoming caller before queries paths inputs
          have candidatePaths : ∀ after, candidate = some after → StatePaths P after.core := by
            intro after selected
            apply SourcePruningEnumerationChildDispatch.observed_cache_paths
              checkEmpty r n p h k scs incoming caller before queries paths inputs after
            simpa only [childEq] using selected
          have finishStopped
              (stopped : some (SourcePruningEnumerationSelectedEdge.Result.stopped []
                (raw, reached, saved, outer, waiting) candidate) = some receipt) :
              ReceiptPaths P receipt := by
            have same := Option.some.inj stopped
            cases same
            exact ⟨outerPaths, candidatePaths⟩
          cases raw with
          | error error => exact finishStopped actual
          | ok payload =>
              cases payload with
              | none => exact finishStopped actual
              | some rows =>
                  cases rows with
                  | nil => exact finishStopped actual
                  | cons first remaining =>
                      cases first with
                      | error error => exact finishStopped actual
                      | ok pair =>
                          rcases pair with ⟨fragment, returned⟩
                          cases remaining with
                          | cons next rest => exact finishStopped actual
                          | nil =>
                              cases candidate with
                              | none => exact finishStopped actual
                              | some after =>
                                  dsimp only at actual
                                  cases finished : SourcePruningEnumerationFinalize.run
                                      reached.checked.native.machine.heap k target fragment after with
                                  | none =>
                                      rw [finished] at actual
                                      cases actual
                                  | some final =>
                                      rw [finished] at actual
                                      have same := Option.some.inj actual
                                      cases same
                                      exact SourcePruningEnumerationFinalize.run_paths
                                        reached.checked.native.machine.heap k target fragment after final
                                        (candidatePaths after rfl) finished

end MicroCFTA.SourcePruningEnumerationPathPreparedOpaque

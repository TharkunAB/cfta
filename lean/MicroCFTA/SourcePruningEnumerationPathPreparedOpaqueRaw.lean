import MicroCFTA.SourcePruningEnumerationPathPreparedOpaque
import MicroCFTA.SourcePruningEnumerationPathObservationRaw

/-!
# Paths in every retained prepared opaque state

The actual opaque dispatcher retains cache paths and successful raw rows.
The same property covers its terminal incoming branch.
-/
namespace MicroCFTA.SourcePruningEnumerationPathPreparedOpaqueRaw
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationPathPreparedOpaque (ReceiptPaths)
open SourcePruningEnumerationPathObservationRaw (ObservationPaths)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat} {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual opaque receipt retains cache paths and all successful raw rows. -/
theorem run_paths
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs) :
    (match SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs incoming caller before queries with
      | none => True
      | some receipt => ReceiptPaths P receipt) ∧
    (match SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs incoming caller before queries with
      | some (.stopped _ observation _) => ObservationPaths P observation
      | _ => True) := by
  refine ⟨SourcePruningEnumerationPathPreparedOpaque.run_paths checkEmpty r n p h k target scs incoming
    caller before queries paths inputs, ?_⟩
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
          trivial
        | rw [← incomingEq] at actual
          generalize childEq : SourcePruningEnumerationChildDispatch.run
            checkEmpty r n p h k scs incoming caller before queries = child at actual
          rcases child with ⟨observation, candidate⟩
          have rawPaths := SourcePruningEnumerationPathObservationRaw.child_paths
            checkEmpty r n p h k scs incoming caller before queries paths inputs
          rw [childEq] at rawPaths
          rcases observation with ⟨raw, reached, saved, outer, waiting⟩
          cases raw with
          | error error => have same := Option.some.inj actual; cases same; exact rawPaths
          | ok payload =>
              cases payload with
              | none => have same := Option.some.inj actual; cases same; exact rawPaths
              | some rows =>
                  cases rows with
                  | nil => have same := Option.some.inj actual; cases same; exact rawPaths
                  | cons first remaining =>
                      cases first with
                      | error error => have same := Option.some.inj actual; cases same; exact rawPaths
                      | ok pair =>
                          rcases pair with ⟨fragment, returned⟩
                          cases remaining with
                          | cons next rest => have same := Option.some.inj actual; cases same; exact rawPaths
                          | nil =>
                              cases candidate with
                              | none => have same := Option.some.inj actual; cases same; exact rawPaths
                              | some after =>
                                  dsimp only at actual
                                  cases finished : SourcePruningEnumerationFinalize.run
                                      reached.checked.native.machine.heap k target fragment after with
                                  | none => rw [finished] at actual; cases actual
                                  | some final =>
                                      rw [finished] at actual
                                      have same := Option.some.inj actual
                                      cases same
                                      trivial

end MicroCFTA.SourcePruningEnumerationPathPreparedOpaqueRaw

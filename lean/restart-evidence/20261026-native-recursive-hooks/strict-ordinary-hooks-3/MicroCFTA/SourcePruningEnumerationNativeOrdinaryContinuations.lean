import MicroCFTA.SourcePruningEnumerationNativeOrdinary
import MicroCFTA.SourcePruningEnumerationNativeContinuations

namespace MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) ×
  EnumerationState.State Symbol Constraint))
variable {width : Nat} {Output Reason : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Enter once and run each completed edge's continuation before its next sibling. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    Raw × Option (SourcePruningEnumerationNativeContinuations.Result Output Reason width) :=
  let raw := ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core)
  (raw, match raw with
    | [.ok ((target, _handle, scs, parent@(.node _ _ _ _)), entered)] =>
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
        else some (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame entered before) (edgesOf parent) caller queries)
    | _ => none)

/-- The wrapper retains every actual entry error, rejection and unsupported observation. -/
theorem entry_readback
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run hook checkEmpty r n p h k uv edgesOf caller before queries).1 =
      ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) := rfl

/-- An actual nonterminal ordinary entry supplies the captured input to the hook-aware fold. -/
theorem entered
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv target handle : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (after : EnumerationState.State Symbol Constraint)
    (observed : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
      [.ok ((target, handle, scs, .node entry edges depth free), after)])
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run hook checkEmpty r n p h k uv edgesOf caller before queries =
      ([.ok ((target, handle, scs, .node entry edges depth free), after)],
        some (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame after before) (edgesOf (.node entry edges depth free)) caller queries)) := by
  simp only [run, observed, nonterminal, Bool.false_eq_true, ↓reduceIte]

/-- An identity continuation preserves the whole ordinary result at every input and bound. -/
theorem identity_run
    (checkEmpty : Bool) (r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    run (SourcePruningEnumerationNativeContinuations.identityHook (Output := Output) (Reason := Reason))
      checkEmpty r n p h k uv edgesOf caller before queries =
      ((SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv edgesOf caller before queries).1,
        (SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv edgesOf caller before queries).2.map
          SourcePruningEnumerationNativeContinuations.ofBranches) := by
  unfold run SourcePruningEnumerationNativeOrdinary.run
  dsimp only
  congr 1
  generalize ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) = rows
  cases rows with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | cons _ _ => rfl
      | nil =>
          cases first with
          | error _ => rfl
          | ok pair =>
              obtain ⟨⟨target, handle, scs, parent⟩, entered⟩ := pair
              cases parent with
              | node entry edges depth free =>
                  by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
                  · simp only [terminal, ↓reduceIte, Option.map_none]
                  · simp only [terminal, ↓reduceIte,
                      SourcePruningEnumerationNativeContinuations.identity_run, Option.map_some]
              | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => rfl

end MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations

import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationFinalize

/-!
# Shared opaque and terminal expansion after preparation

The input value is already prepared. This worker does not unfold it.
Finalization writes the original target. A failed finalization retains the
actual child endpoint and its cache before finalization.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Child" => SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Expand a prepared opaque or terminal value at its original target. -/
noncomputable def run (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (value : Node) (caller : Caller width) (before : Cached)
    (queries : Queries) : Option (Receipt width) :=
  if value = .empty then some (.rejected caller queries before)
  else if (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) then none
  else
    match Child checkEmpty r n p h k scs value caller before queries with
    | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
        match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
        | some finished => some (.complete fragment reached saved finished)
        | none => some (.finalizeStopped fragment reached saved after)
    | (observation, candidate) => some (.stopped [] observation candidate)

/-- Empty input rejects at the actual entry endpoint and cache. -/
theorem empty (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    run checkEmpty r n p h k target scs .empty caller before queries =
      some (.rejected caller queries before) := by
  simp only [run, ↓reduceIte]

/-- Ordinary nonterminal values use the separate alternative scan. -/
theorem ordinary_deferred (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run checkEmpty r n p h k target scs (.node entry edges depth free) caller before queries = none := by
  simp only [run, reduceCtorEq, ↓reduceIte, nonterminal, Bool.not_false]

/-- Terminal input retains the literal child and finalizer observations. -/
theorem terminal_step (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (value : Node) (caller : Caller width) (before : Cached)
    (queries : Queries) (nonempty : value ≠ .empty)
    (terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true) :
    run checkEmpty r n p h k target scs value caller before queries =
      match Child checkEmpty r n p h k scs value caller before queries with
      | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
          match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
          | some finished => some (.complete fragment reached saved finished)
          | none => some (.finalizeStopped fragment reached saved after)
      | (observation, candidate) => some (.stopped [] observation candidate) := by
  have gate : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false := by
    cases value <;> simp only [terminal, Bool.not_true]
  simp only [run, ite_eq_right nonempty, gate, Bool.false_eq_true, ↓reduceIte]

/-- A failed finalizer retains the child's returned endpoint and cache. -/
theorem finalize_stopped (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (value : Node) (caller reached : Caller width) (before after : Cached)
    (queries saved : Queries) (fragment : Fragment) (returned outer : Core)
    (waiting : EnumerationWaitingIndex.Waiting)
    (nonempty : value ≠ .empty)
    (eligible : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (child : Child checkEmpty r n p h k scs value caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some after))
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after = none) :
    run checkEmpty r n p h k target scs value caller before queries =
      some (.finalizeStopped fragment reached saved after) := by
  simp only [run, ite_eq_right nonempty, eligible, Bool.false_eq_true, ↓reduceIte, child, finalized]

/-- A successful finalizer supplies its literal completed cache. -/
theorem finalized (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (value : Node) (caller reached : Caller width) (before after finished : Cached)
    (queries saved : Queries) (fragment : Fragment) (returned outer : Core)
    (waiting : EnumerationWaitingIndex.Waiting)
    (nonempty : value ≠ .empty)
    (eligible : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (child : Child checkEmpty r n p h k scs value caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some after))
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after = some finished) :
    run checkEmpty r n p h k target scs value caller before queries =
      some (.complete fragment reached saved finished) := by
  simp only [run, ite_eq_right nonempty, eligible, Bool.false_eq_true, ↓reduceIte, child, finalized]

end MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch

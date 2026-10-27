import MicroCFTA.SourcePruningEnumerationHookInvocation
import MicroCFTA.SourcePruningEnumerationRecursive

/-!
# Actual entry and callback receipts on an output path

The ordinary wrapper retains its actual entry row and captured scan input.
An emitted callback output requires its actual false recording receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationHookInvocation
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "FoldResult" => SourcePruningEnumerationNativeContinuations.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the entry row, its nonterminal bucket and the actual sibling invocation. -/
def OrdinaryInvocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached) : Prop :=
  ∃ target handle scs entry rows depth free entered,
    ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
      [.ok ((target, handle, scs, .node entry rows depth free), entered)] ∧
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
    Invocation hook checkEmpty r n p h k target scs (EnumerationExpandableIndex.frame entered before)
      (edgesOf (.node entry rows depth free)) caller queries fragment reached saved after

/-- Every actual ordinary output retains the entry and the literal hook invocation that emitted it. -/
theorem ordinary_output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (result : FoldResult Output Reason width)
    (observed : (SourcePruningEnumerationNativeOrdinaryContinuations.run hook checkEmpty r n p h k uv
      edgesOf caller before queries).2 = some result) :
    ∀ output ∈ foldOutputs result,
      ∃ fragment reached saved after,
        OrdinaryInvocation hook checkEmpty r n p h k uv edgesOf caller before queries fragment reached saved after ∧
        output ∈ hookOutputs (hook fragment reached saved after) := by
  unfold SourcePruningEnumerationNativeOrdinaryContinuations.run at observed
  dsimp only at observed
  split at observed
  · split at observed
    · cases observed
    · have same := Option.some.inj observed
      subst result
      rename_i raw target handle scs entry rows depth free entered entryRead nonterminal
      intro output member
      obtain ⟨fragment, reached, saved, after, invocation, emitted⟩ :=
        run_output_invocation hook checkEmpty r n p h k _ _ _ _ caller queries output member
      refine ⟨fragment, reached, saved, after, ?_, emitted⟩
      refine ⟨target, handle, scs, entry, rows, depth, free, entered, entryRead, ?_, invocation⟩
      simpa only [Bool.not_eq_true] using nonterminal
  · cases observed

end MicroCFTA.SourcePruningEnumerationHookInvocation

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationHookInvocation (hookOutputs foldOutputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Typing : Type} {Output : Type u} {Reason : Type v}

/-- An emitted callback output has the exact false record receipt and the same native endpoint. -/
theorem continueWith_output_restart
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next →
      Result (SourcePruningEnumerationRecursive.Output width Typing) (Failure width Typing) width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ hookOutputs (continueWith recur graph templates stop order fuel metadata uv fragment caller queries before),
      ∃ updated core,
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv (.inl fragment) before.core) =
          [.ok ((false, updated), core)] ∧
        output ∈ hookOutputs (recur updated caller queries (EnumerationExpandableIndex.frame core before)
          (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core before))) := by
  unfold continueWith
  dsimp only
  split
  · intro output member; cases member
  · intro output member
    exact ⟨_, _, by assumption, member⟩
  · intro output member; cases member

/-- Finishing a scan retains its outputs at both complete and stopped outcomes. -/
theorem finish_hook_outputs (uv : Nat)
    (result : SourcePruningEnumerationNativeContinuations.Result
      (SourcePruningEnumerationRecursive.Output width Typing) (Failure width Typing) width) :
    hookOutputs (finish uv result) = foldOutputs result := by
  cases result <;> rfl

end MicroCFTA.SourcePruningEnumerationRecursive

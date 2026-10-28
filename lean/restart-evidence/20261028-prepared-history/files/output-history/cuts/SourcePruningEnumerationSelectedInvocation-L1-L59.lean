import MicroCFTA.SourcePruningEnumerationSelectedContinuations
import MicroCFTA.SourcePruningEnumerationHookInvocation

/-!
# Actual hook paths after native preparation

Each output retains the exact entry and native preparation result.
Ordinary paths retain the preceding sibling endpoints.
Opaque and terminal paths retain their actual completed receipt.
The original stored handle and prepared value remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedContinuations
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
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "Fold" => SourcePruningEnumerationNativeContinuations.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the actual preparation and selected branch that invokes a hook. -/
def Invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached) : Prop :=
  ∃ (target handle : Nat) (scs : List Suspended) (decoded value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core),
    SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)) ∧
    if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
      SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (EnumerationExpandableIndex.frame entered before) queries =
          some (.complete fragment reached saved after)
    else match value with
    | parent@(.node ..) =>
        SourcePruningEnumerationHookInvocation.Invocation hook checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame entered before) (edgesOf parent)
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
          fragment reached saved after
    | _ =>
        SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
          (EnumerationExpandableIndex.frame entered before) queries =
            some (.complete fragment reached saved after)

end

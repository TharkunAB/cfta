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

/-- A singleton receipt can emit an output only through its completed-fragment hook. -/
theorem receipt_output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (receipt : Option (Receipt width)) :
    ∀ output ∈ foldOutputs (SourcePruningEnumerationReceiptContinuation.run hook receipt),
      ∃ fragment reached saved after,
        receipt = some (.complete fragment reached saved after) ∧
          output ∈ hookOutputs (hook fragment reached saved after) := by
  cases receipt with
  | none => intro output member; cases member
  | some receipt =>
      cases receipt with
      | unhandled => intro output member; cases member
      | rejected caller queries after => intro output member; cases member
      | complete fragment caller queries after =>
          cases actual : hook fragment caller queries after <;> intro output member
          all_goals
            refine ⟨fragment, caller, queries, after, rfl, ?_⟩
            simpa only [SourcePruningEnumerationReceiptContinuation.run, actual, foldOutputs, hookOutputs] using member
      | stopped fragments observation candidate =>
          cases actual : SourcePruningEnumerationNativeBranches.advance (.stopped fragments observation candidate) with
          | none =>
              intro output member
              simp only [SourcePruningEnumerationReceiptContinuation.run, actual, foldOutputs, List.not_mem_nil] at member
          | some endpoint =>
              obtain ⟨caller, queries⟩ := endpoint
              intro output member
              simp only [SourcePruningEnumerationReceiptContinuation.run, actual, foldOutputs, List.not_mem_nil] at member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual selected output retains its actual preparation and hook invocation. -/
theorem output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (folded : Fold Output Reason width)
    (observed : (run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).2 =
      some folded) :
    ∀ output ∈ foldOutputs folded,
      ∃ fragment reached saved after,
        Invocation hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries
          fragment reached saved after ∧ output ∈ hookOutputs (hook fragment reached saved after) := by
  unfold run at observed
  generalize preparation : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
    prepared at observed
  obtain ⟨raw, native⟩ := prepared
  cases native with
  | none => cases observed
  | some native =>
      cases native with
      | failed fault heap => cases observed
      | done value heap =>
          cases raw with
          | nil => cases observed
          | cons row rest =>
              cases row with
              | error error => cases observed
              | ok row =>
                  cases rest with
                  | cons row rest => cases observed
                  | nil =>
                      obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := row
                      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
                      · simp only [terminal, ↓reduceIte] at observed
                        have same := Option.some.inj observed
                        subst folded
                        intro output member
                        obtain ⟨fragment, reached, saved, after, actual, emitted⟩ :=
                          receipt_output_invocation hook _ output member
                        refine ⟨fragment, reached, saved, after,
                          ⟨target, handle, scs, decoded, value, heap, entered, preparation, ?_⟩, emitted⟩
                        simpa only [terminal, ↓reduceIte] using actual
                      · simp only [terminal, Bool.false_eq_true, ↓reduceIte] at observed
                        cases value with
                        | node entry edges depth free =>
                            have same := Option.some.inj observed
                            subst folded
                            intro output member
                            obtain ⟨fragment, reached, saved, after, actual, emitted⟩ :=
                              SourcePruningEnumerationHookInvocation.run_output_invocation
                                hook checkEmpty r n p h k target scs
                                (EnumerationExpandableIndex.frame entered before)
                                (edgesOf (.node entry edges depth free))
                                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries output member
                            refine ⟨fragment, reached, saved, after,
                              ⟨target, handle, scs, decoded, .node entry edges depth free, heap, entered,
                                preparation, ?_⟩, emitted⟩
                            simpa only [terminal, Bool.false_eq_true, ↓reduceIte] using actual
                        | empty | mu _ _ _ _ | reference _ | union _ _ _ _ =>
                            have same := Option.some.inj observed
                            subst folded
                            intro output member
                            obtain ⟨fragment, reached, saved, after, actual, emitted⟩ :=
                              receipt_output_invocation hook _ output member
                            refine ⟨fragment, reached, saved, after,
                              ⟨target, handle, scs, decoded, _, heap, entered, preparation, ?_⟩, emitted⟩
                            simpa only [terminal, Bool.false_eq_true, ↓reduceIte] using actual

end MicroCFTA.SourcePruningEnumerationSelectedContinuations

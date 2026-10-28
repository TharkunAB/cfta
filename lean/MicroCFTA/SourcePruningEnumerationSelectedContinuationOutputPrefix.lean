import MicroCFTA.SourcePruningEnumerationNativeContinuationOutputPrefix
import MicroCFTA.SourcePruningEnumerationSelectedContinuations

/-!
# Ordered output prefixes through actual selected dispatch

Completed hooks keep their exact outputs and native endpoint.
Every replacement hook retains its earlier output list as a prefix.
The actual selected preparation stays fixed for both hooks.
Complete and stopped dispatch results retain the same output prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationReceiptContinuation
open EnumerationState
open SourcePruningEnumerationHookInvocation (hookOutputs foldOutputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- The actual single-receipt dispatch retains its complete or stopped output prefix. -/
theorem run_outputs_prefix
    (first second : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (same : ∀ fragment reached saved after outputs middleCaller middleQueries,
      first fragment reached saved after = .complete outputs middleCaller middleQueries →
      second fragment reached saved after = .complete outputs middleCaller middleQueries)
    (prefixHooks : ∀ fragment reached saved after,
      List.IsPrefix (hookOutputs (first fragment reached saved after))
        (hookOutputs (second fragment reached saved after)))
    (current : Option (Receipt width)) :
    List.IsPrefix (foldOutputs (run first current)) (foldOutputs (run second current)) := by
  cases current with
  | none => exact List.prefix_rfl
  | some receipt =>
      cases receipt with
      | complete fragment reached saved after =>
          cases continued : first fragment reached saved after with
          | complete outputs middleCaller middleQueries =>
              have next := same fragment reached saved after outputs middleCaller middleQueries continued
              simp only [run, continued, next, foldOutputs]
              exact List.prefix_rfl
          | stopped outputs reason endpoint =>
              have retained := prefixHooks fragment reached saved after
              cases next : second fragment reached saved after <;>
                simpa only [run, continued, next, hookOutputs, foldOutputs] using retained
      | rejected reached saved after => exact List.prefix_rfl
      | stopped fragments observation candidate => exact List.prefix_rfl
      | unhandled => exact List.prefix_rfl

end MicroCFTA.SourcePruningEnumerationReceiptContinuation

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
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual selected dispatch retains its output prefix at the same preparation and native fuels. -/
theorem run_outputs_prefix
    (first second : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (same : ∀ fragment reached saved after outputs middleCaller middleQueries,
      first fragment reached saved after = .complete outputs middleCaller middleQueries →
      second fragment reached saved after = .complete outputs middleCaller middleQueries)
    (prefixHooks : ∀ fragment reached saved after,
      List.IsPrefix (hookOutputs (first fragment reached saved after))
        (hookOutputs (second fragment reached saved after))) :
    List.IsPrefix
      (((run first checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).2.map
        foldOutputs).getD [])
      (((run second checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).2.map
        foldOutputs).getD []) := by
  unfold run
  generalize preparation : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before = original
  obtain ⟨raw, native⟩ := original
  dsimp only
  cases native with
  | none => exact List.prefix_rfl
  | some result =>
      cases result with
      | failed fault heap => exact List.prefix_rfl
      | done value heap =>
          cases raw with
          | nil => exact List.prefix_rfl
          | cons firstRow rest =>
              cases rest with
              | cons secondRow tail => cases firstRow <;> exact List.prefix_rfl
              | nil =>
                  cases firstRow with
                  | error error => exact List.prefix_rfl
                  | ok pair =>
                      obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := pair
                      dsimp only
                      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
                      · simp only [terminal]
                        exact SourcePruningEnumerationReceiptContinuation.run_outputs_prefix
                          first second same prefixHooks _
                      · simp only [terminal]
                        cases value with
                        | node entry edges depth free =>
                            exact SourcePruningEnumerationNativeContinuations.run_outputs_prefix
                              first second checkEmpty r n p h k target scs
                              (EnumerationExpandableIndex.frame entered before) same prefixHooks
                              (edgesOf (.node entry edges depth free))
                              (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                        | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                            exact SourcePruningEnumerationReceiptContinuation.run_outputs_prefix
                              first second same prefixHooks _

end MicroCFTA.SourcePruningEnumerationSelectedContinuations

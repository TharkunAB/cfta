import MicroCFTA.SourcePruningEnumerationNativeContinuationCompletedCongruence
import MicroCFTA.SourcePruningEnumerationSelectedContinuations

/-!
# Completed selected dispatch under a changed hook

The actual preparation and captured native inputs stay fixed.
Agreement on completed hook results retains each exact completed dispatch.
Stopped hooks need not agree.
-/
namespace MicroCFTA.SourcePruningEnumerationReceiptContinuation
open EnumerationState
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

/-- Preserve the exact completed single-receipt dispatch under agreement on completed hooks. -/
theorem run_complete_congr
    (first second : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (same : ∀ fragment reached saved after outputs middleCaller middleQueries,
      first fragment reached saved after = .complete outputs middleCaller middleQueries →
      second fragment reached saved after = .complete outputs middleCaller middleQueries)
    (current : Option (Receipt width)) (processed : List (Receipt width))
    (outputs : List Output) (finalCaller : Caller width) (finalQueries : Queries)
    (actual : run first current = .complete processed outputs finalCaller finalQueries) :
    run second current = .complete processed outputs finalCaller finalQueries := by
  cases current with
  | none => cases actual
  | some receipt =>
      cases receipt with
      | complete fragment reached saved after =>
          cases continued : first fragment reached saved after with
          | stopped headOutputs reason endpoint =>
              simp only [run, continued, reduceCtorEq] at actual
          | complete headOutputs middleCaller middleQueries =>
              have next := same fragment reached saved after headOutputs middleCaller middleQueries continued
              simp only [run, continued] at actual
              simpa only [run, next] using actual
      | rejected reached saved after => exact actual
      | stopped fragments observation candidate => exact actual
      | unhandled => exact actual

end MicroCFTA.SourcePruningEnumerationReceiptContinuation

namespace MicroCFTA.SourcePruningEnumerationSelectedContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Preserve the exact completed fold after the same actual selected preparation. -/
theorem run_complete_congr
    (first second : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (same : ∀ fragment reached saved after outputs middleCaller middleQueries,
      first fragment reached saved after = .complete outputs middleCaller middleQueries →
      second fragment reached saved after = .complete outputs middleCaller middleQueries)
    (processed : List (Receipt width)) (outputs : List Output)
    (finalCaller : Caller width) (finalQueries : Queries)
    (actual : (run first checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).2 =
      some (.complete processed outputs finalCaller finalQueries)) :
    (run second checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).2 =
      some (.complete processed outputs finalCaller finalQueries) := by
  unfold run at actual ⊢
  generalize preparation : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
    original at actual ⊢
  obtain ⟨raw, native⟩ := original
  dsimp only at actual ⊢
  cases native with
  | none => cases actual
  | some result =>
      cases result with
      | failed fault heap => cases actual
      | done value heap =>
          cases raw with
          | nil => cases actual
          | cons firstRow rest =>
              cases rest with
              | cons secondRow tail => cases firstRow <;> cases actual
              | nil =>
                  cases firstRow with
                  | error error => cases actual
                  | ok pair =>
                      obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := pair
                      dsimp only at actual ⊢
                      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
                      · simp only [terminal] at actual ⊢
                        exact congrArg some (SourcePruningEnumerationReceiptContinuation.run_complete_congr
                          first second same _ processed outputs finalCaller finalQueries (Option.some.inj actual))
                      · simp only [terminal] at actual ⊢
                        cases value with
                        | node entry edges depth free =>
                            exact congrArg some
                              (SourcePruningEnumerationNativeContinuations.run_complete_congr first second
                                checkEmpty r n p h k target scs (EnumerationExpandableIndex.frame entered before)
                                same (edgesOf (.node entry edges depth free))
                                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                                processed outputs finalCaller finalQueries (Option.some.inj actual))
                        | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                            exact congrArg some
                              (SourcePruningEnumerationReceiptContinuation.run_complete_congr first second same _
                                processed outputs finalCaller finalQueries (Option.some.inj actual))

end MicroCFTA.SourcePruningEnumerationSelectedContinuations

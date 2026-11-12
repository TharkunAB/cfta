import MicroCFTA.SourcePruningEnumerationSharedPreparedContinuations
import MicroCFTA.SourcePruningEnumerationSharedEagerChildren

/-!
# Child policies in the actual common preparation operation

One selected preparation supplies the entry and native outcome.
Only the ordinary row scan receives a child policy.
Terminal, opaque and failure branches retain the existing operations.
The shallow adapter preserves the entire old preparation and fold result.
This module does not replace the recursive or selected-root driver.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedChildVisitors (visitCapturedWith shallowVisit run_eq_scan_shallow)
open SourcePruningEnumerationSharedEagerChildren (eagerChild)
open SourcePruningEnumerationSharedBranching (scan)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Preparation" => SourcePruningEnumerationSharedPreparedContinuations.Preparation
local notation "HookResult" => NativeContinuations.HookResult
local notation "Fold" => NativeContinuations.Result
local notation "Observation" => ChildDispatch.Observation
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold Output Reason width) →
  (Observation width → Option Cached → Fold Output Reason width) → Fold Output Reason width
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Prepare once and use the supplied child operation only inside the ordinary row scan. -/
noncomputable def runWithChild
    (child : Visitor)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    Preparation × Option (Fold Output Reason width) :=
  let observation := SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before
  (observation, match observation.2 with
    | some (.done value heap) =>
        match observation.1 with
        | [.ok ((target, _handle, scs, _decoded), entered)] =>
            some (if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
              SourcePruningEnumerationSharedReceiptContinuation.run hook
                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                  (EnumerationExpandableIndex.frame entered before) queries)
            else match value with
              | parent@(.node ..) =>
                  scan (visitCapturedWith child hook k target scs)
                    (EnumerationExpandableIndex.frame entered before) (edgesOf parent)
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
              | _ =>
                  SourcePruningEnumerationSharedReceiptContinuation.run hook
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                    (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
                      (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                      (EnumerationExpandableIndex.frame entered before) queries))
        | _ => none
    | _ => none)

/-- Install the actual eager child visitor in this same common preparation path. -/
noncomputable def runEager
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    Preparation × Option (Fold Output Reason width) :=
  runWithChild (eagerChild checkEmpty r n p h k edgesOf) hook
    checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries

/-- The shallow policy preserves the entire old preparation, fold, receipts and endpoints. -/
theorem runWithChild_shallow
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    runWithChild (shallowVisit checkEmpty r n p h k) hook
        checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      SourcePruningEnumerationSharedPreparedContinuations.run hook
        checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries := by
  unfold runWithChild SourcePruningEnumerationSharedPreparedContinuations.run
  simp only [← run_eq_scan_shallow]
  rfl

/-- Retain every actual entry row and native preparation outcome for any child operation. -/
theorem preparation_readback
    (child : Visitor)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    (runWithChild child hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).1 =
      SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before := rfl

/-- Eager descent retains the same actual selected preparation observation. -/
theorem runEager_preparation_readback
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    (runEager hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).1 =
      SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before := rfl

/-- A native preparation fault retains its exact returned heap before any child or hook runs. -/
theorem failed
    (child : Visitor)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries)
    (raw : List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) ×
      EnumerationState.State Symbol Constraint)))
    (fault : MergedSourceComparison.Fault) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      (raw, some (.failed fault heap))) :
    runWithChild child hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      ((raw, some (.failed fault heap)), none) := by
  simp only [runWithChild, observed]

end MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy

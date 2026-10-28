import MicroCFTA.SourcePruningEnumerationBoundaryAction
import MicroCFTA.SourcePruningEnumerationKeyShapeBudget
import MicroCFTA.SourcePruningEnumerationBoundaryFreshness
import MicroCFTA.SourcePruningEnumerationModelKeyShapes

/-!
# Original model budgets at an actual checked boundary action

The actual false check derives freshness at its returned representative.
Actual boundary narrowing retains the handle and selects an identity action.
The original stored model derives membership in the finite shape carrier.
Inserting this same checked key then strictly decreases its handle budget.
The full later prefix and entry connection remains a separate operation.
-/
namespace MicroCFTA.SourcePruningEnumerationCheckedBoundaryBudget
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationOrigins
open SourcePruningEnumerationModelKeyShapes SourcePruningEnumerationKeyShapeBudget
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing Key : Type}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Actual check and boundary action observations derive a finite unused shape without a freshness input. -/
theorem checked_action_shape_budget [DecidableEq (EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : Metadata Typing)
    (checkFuel nativeFuel representativeFuel uv handle : Nat) (scs : List Suspended)
    (value result : Value Symbol NativeGuard)
    (heap afterHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before checked afterCore : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard Unit)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (available : Available heap value) (closed : value.free = [])
    (decoded : lookupNode heap handle = some value) (encoded : encodeNode value = some handle)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv handle scs)
      before false checked)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv handle scs value heap = .done (result, some action) afterHeap)
    (boundary : MergedOrdinaryHeight.recursiveBoundary result = true)
    (executed : Success action checked () afterCore)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before)
    (origins : AssignmentOrigins whole before.counter assignment)
    (canonical : EnumerationValidity.Canonical before) (inside : uv < before.counter)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∃ root, result = value ∧ afterHeap = heap ∧ afterCore = checked ∧
      Success (representative checkFuel uv) before root afterCore ∧
      (recursionKey handle scs).tries ∈ unused (keyShapes whole) handle (afterCore.recursionAncestry root) ∧
      (unused (keyShapes whole) handle
        (recursionKey handle scs :: afterCore.recursionAncestry root).eraseDups).length <
        (unused (keyShapes whole) handle (afterCore.recursionAncestry root)).length := by
  have retained := SourcePruningEnumerationAction.prepare_boundary_retained holeKey fits admits metadata
    nativeFuel representativeFuel uv handle scs value heap result (some action) afterHeap
    ready available closed encoded prepared boundary
  have actionSame : action = pure () := Option.some.inj retained.2.2
  have coreSame : afterCore = checked := (success_pure () () checked afterCore).mp
    (by simpa only [actionSame] using executed) |>.2
  have originalBoundary : MergedOrdinaryHeight.recursiveBoundary value = true := by
    simpa only [retained.1] using boundary
  obtain ⟨root, resolving, fresh⟩ := SourcePruningEnumerationRecursionOrder.checkRepeated_false_fresh
    heap checkFuel uv handle scs value before checked decoded originalBoundary checking
  have member := stored_recursion_key_mem language meaning before whole assignment satisfied origins
    canonical inside stored
  subst afterCore
  refine ⟨root, retained.1, retained.2.1, rfl, resolving, ?_, ?_⟩
  · simp only [unused, List.mem_filter, decide_eq_true_eq]
    exact ⟨member, fresh⟩
  · exact unused_insert_lt (keyShapes whole) (recursionKey handle scs)
      (checked.recursionAncestry root) member fresh

end MicroCFTA.SourcePruningEnumerationCheckedBoundaryBudget

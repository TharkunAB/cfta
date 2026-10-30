import MicroCFTA.SourcePruningEnumerationCheckedBoundaryBudget
import MicroCFTA.SourcePruningEnumerationBoundaryEntryBudget
import MicroCFTA.SourcePruningEnumerationPathKeyShapes

/-!
# Original path-shape consumption at actual boundary observations

The fixed finite path domain bounds every actual stored recursion-key shape.
The actual false check derives freshness at its returned representative.
The boundary action and entry retain their exact frames and history updates.
No satisfying term or assignment model is required. Native handles remain free.
-/
namespace MicroCFTA.SourcePruningEnumerationPathBoundaryBudget
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourcePruningEnumerationPathKeyShapes SourcePruningEnumerationKeyShapeBudget
open SourcePruningEnumerationPathTransport
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing Key : Type}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Actual boundary observations consume a finite original path shape without a term model. -/
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
    (domain : List EqualityTrie.Path)
    (paths : StatePaths (fun path => path ∈ domain) before)
    (canonical : EnumerationValidity.Canonical before)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∃ root, result = value ∧ afterHeap = heap ∧ afterCore = checked ∧
      Success (representative checkFuel uv) before root afterCore ∧
      (recursionKey handle scs).tries ∈ unused (keyShapes domain) handle (afterCore.recursionAncestry root) ∧
      (unused (keyShapes domain) handle
        (recursionKey handle scs :: afterCore.recursionAncestry root).eraseDups).length <
        (unused (keyShapes domain) handle (afterCore.recursionAncestry root)).length := by
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
  have member := stored_recursion_key_mem domain before paths canonical stored
  subst afterCore
  refine ⟨root, retained.1, retained.2.1, rfl, resolving, ?_, ?_⟩
  · simp only [unused, List.mem_filter, decide_eq_true_eq]
    exact ⟨member, fresh⟩
  · exact unused_insert_lt (keyShapes domain) (recursionKey handle scs)
      (checked.recursionAncestry root) member fresh

/-- The actual entry consumes a finite original path shape after the actual false boundary check. -/
theorem checked_enter_shape_budget
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (checkFuel entryFuel uv target handle : Nat) (bucket : List Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before checked entering after : EnumerationState.State Symbol EnumGuard)
    (total : UnionFind.Total before.representatives)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv handle bucket)
      before false checked)
    (intervening : Frame checked entering)
    (entered : ExceptT.run (SourcePruningEnumerationEntry.enter heap entryFuel uv entering) =
      [.ok ((target, handle, bucket, value), after)])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (domain : List EqualityTrie.Path)
    (paths : StatePaths (fun path => path ∈ domain) before)
    (canonical : EnumerationValidity.Canonical before)
    (stored : before.values[uv]? = some (.unenumerated (some handle) bucket)) :
    lookupNode heap handle = some value ∧
      Success (representative checkFuel uv) before target checked ∧
      after.recursionAncestry = before.recursionAncestry ∧
      after.expansionAncestry =
        (recursionKey handle bucket :: checked.recursionAncestry target).eraseDups ∧
      (recursionKey handle bucket).tries ∈
        unused (keyShapes domain) handle (checked.recursionAncestry target) ∧
      (unused (keyShapes domain) handle after.expansionAncestry).length <
        (unused (keyShapes domain) handle (checked.recursionAncestry target)).length := by
  have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
    heap checkFuel uv handle bucket before checked total checking
  have fullFrame := checkFrame.trans intervening
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter heap entryFuel uv)
      entering (target, handle, bucket, value) after := by
    rw [Success, entered]
    exact List.mem_singleton_self _
  obtain ⟨size, targetPath, decoded, histories, expansion⟩ :=
    SourcePruningEnumerationEntry.enter_history heap entryFuel uv entering after target handle bucket value
      (fullFrame.total total) entrySuccess
  obtain ⟨root, resolving, fresh⟩ := SourcePruningEnumerationRecursionOrder.checkRepeated_false_fresh
    heap checkFuel uv handle bucket value before checked decoded boundary checking
  obtain ⟨found, foundRun, rootSame, _checkedSame⟩ :=
    (EnumerationSchedule.representative_success checkFuel uv before checked root).mp resolving
  have rootPath : UnionFind.Reaches before.representatives uv root found.size := by
    rw [rootSame]
    exact (UnionFind.findRoot_correct checkFuel before.representatives uv found foundRun).1
  have same : root = target :=
    (UnionFind.reaches_unique rootPath ((fullFrame.reaches uv target size).mp targetPath)).1
  rw [same] at resolving fresh
  have member := stored_recursion_key_mem domain before paths canonical stored
  have expansionSame : after.expansionAncestry =
      (recursionKey handle bucket :: checked.recursionAncestry target).eraseDups := by
    simpa only [boundary, ↓reduceIte, intervening.recursionAncestry] using expansion
  refine ⟨decoded, resolving, histories.trans fullFrame.recursionAncestry, expansionSame, ?_, ?_⟩
  · simp only [unused, List.mem_filter, decide_eq_true_eq]
    exact ⟨member, fresh⟩
  · rw [expansionSame]
    exact unused_insert_lt (keyShapes domain) (recursionKey handle bucket)
      (checked.recursionAncestry target) member fresh

end MicroCFTA.SourcePruningEnumerationPathBoundaryBudget

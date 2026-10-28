import MicroCFTA.SourcePruningEnumerationRecursionOrder

/-!
# Fresh keys at an actual false native boundary check

The successful false branch excludes its exact checked key.
The representative and returned state come from the actual check.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursionOrder
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- A successful false boundary check excludes its key at the actual resolved representative. -/
theorem checkRepeated_false_fresh
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before false after) :
    ∃ root, Success (representative fuel uv) before root after ∧
      recursionKey handle scs ∉ after.recursionAncestry root := by
  simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
  obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
  by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry root
  · simp [Success, setValue, get, getThe, MonadStateOf.get, modify, modifyGet,
      MonadStateOf.modifyGet, bind, pure, StateT.pure, StateT.bind, StateT.get, StateT.modifyGet,
      ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run, seen] at continued
  · have same : after = resolved := by
      simpa [Success, get, getThe, MonadStateOf.get, bind, pure, StateT.pure, StateT.bind,
        StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
        ExceptT.run, seen, eq_comm] using continued
    subst after
    exact ⟨root, resolution, seen⟩

end MicroCFTA.SourcePruningEnumerationRecursionOrder

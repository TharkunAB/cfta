import MicroCFTA.EnumerationFlatPartial
import MicroCFTA.SourcePruningEnumerationRecursion

/-!
# Native recursion checks with direct-parent forests

The check reads the same native node and recursion ancestry. A repeated key
clears the bucket at the actual representative. Index repair remains separate.
-/

namespace MicroCFTA.SourceFlatPruningRecursion

open EnumerationState EnumerationFlatState EnumerationResultRelation
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Check the native boundary and clear only a repeated recursion key. -/
def checkRepeated (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv handle : Nat) (scs : List Suspended) : Action Symbol EnumGuard Bool := do
  match lookupNode heap handle with
  | none => EnumerationFlatState.failure .unresolvedReference
  | some value =>
      if MergedOrdinaryHeight.recursiveBoundary value then
        let root ← EnumerationFlatState.representative uv
        let current : EnumerationFlatState.State Symbol EnumGuard ← get
        if recursionKey handle scs ∈ current.recursionAncestry root then
          EnumerationFlatState.setValue root (.unenumerated (some handle) [])
          pure true
        else pure false
      else pure false

/-- A completed old read preserves every check row and the complete returned core. -/
theorem checkRepeated_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv handle : Nat) (scs : List Suspended)
    (completed : UnionFind.findRoot fuel earlier.representatives uv = some found) :
    Results Related (checkRepeated (EnumGuard := EnumGuard) heap uv handle scs flat)
      (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs earlier) := by
  unfold checkRepeated SourcePruningEnumerationRecursion.checkRepeated
  cases decoded : lookupNode heap handle with
  | none => exact failure_related .unresolvedReference
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [boundary, ↓reduceIte]
        apply stateT_bind _ _ _ _ (representative_related related completed)
        intro root left right states
        change Results Related
          ((if recursionKey handle scs ∈ left.recursionAncestry root then
            EnumerationFlatState.setValue root (.unenumerated (some handle) []) >>= fun _ => pure true
           else pure false) left)
          ((if recursionKey handle scs ∈ right.recursionAncestry root then
            EnumerationState.setValue root (.unenumerated (some handle) []) >>= fun _ => pure true
           else pure false) right)
        rw [states.recursionAncestry]
        split
        · apply stateT_bind _ _ _ _ (setValue_related states root (.unenumerated (some handle) []))
          intro _ _ _ related
          exact pure_related related true
        · exact pure_related states false
      · simp only [boundary]
        exact pure_related related false

/-- Related input forests derive a stable sufficient old recursion-read bound. -/
theorem checkRepeated_stable (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv handle : Nat) (scs : List Suspended) :
    ∃ fuel, ∀ extra, Results Related (checkRepeated (EnumGuard := EnumGuard) heap uv handle scs flat)
      (SourcePruningEnumerationRecursion.checkRepeated heap (fuel + extra) uv handle scs earlier) := by
  obtain ⟨fuel, found, stable, _path, _size, _forest⟩ :=
    FlatUnionFind.find_stable related.representatives uv
  exact ⟨fuel, fun extra => checkRepeated_related related heap uv handle scs (stable extra)⟩

end MicroCFTA.SourceFlatPruningRecursion

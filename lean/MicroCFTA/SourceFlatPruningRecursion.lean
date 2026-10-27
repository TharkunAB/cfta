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
        simp only [Bind.bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, ExceptT.pure,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
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

/-- Replay the actual successful check without a lookup premise on unused branches. -/
theorem checkRepeated_replays
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended) :
    EnumerationFlatReplay.Replays (checkRepeated (EnumGuard := EnumGuard) heap uv handle scs)
      (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs) := by
  unfold checkRepeated SourcePruningEnumerationRecursion.checkRepeated
  cases decoded : lookupNode heap handle with
  | none =>
      intro flat earlier result after _ observed
      exact (EnumerationCorrectness.success_failure .unresolvedReference earlier after result observed).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [boundary, ↓reduceIte]
        apply EnumerationFlatReplay.bind_replays _ _ _ _
          (EnumerationFlatReplay.representative_replays fuel uv)
        intro root flat earlier result after related observed
        simp only [EnumerationCorrectness.Success, Bind.bind, StateT.bind, ExceptT.bind,
          ExceptT.bindCont, ExceptT.mk, get, getThe, MonadStateOf.get, StateT.get,
          Pure.pure, ExceptT.pure, ExceptT.run, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at observed ⊢
        change EnumerationCorrectness.Success
          (if recursionKey handle scs ∈ earlier.recursionAncestry root then
            EnumerationState.setValue root (.unenumerated (some handle) []) >>= fun _ => pure true
           else pure false) earlier result after at observed
        change ∃ next,
          ((if recursionKey handle scs ∈ flat.recursionAncestry root then
              EnumerationFlatState.setValue root (.unenumerated (some handle) []) >>= fun _ => pure true
            else pure false) flat) = [.ok (result, next)] ∧ Related next after
        rw [related.recursionAncestry]
        by_cases seen : recursionKey handle scs ∈ earlier.recursionAncestry root
        · simp only [seen, ↓reduceIte] at observed ⊢
          obtain ⟨token, middle, written, returned⟩ :=
            (EnumerationCorrectness.success_bind _ _ earlier result after).mp observed
          cases token
          have shape := (EnumerationDriver.modify_success _ earlier middle).mp written
          obtain ⟨rfl, rfl⟩ := (EnumerationCorrectness.success_pure true result middle after).mp returned
          refine ⟨{flat with values := flat.values.set root (.unenumerated (some handle) [])}, rfl, ?_⟩
          rw [shape]
          exact ⟨related.valid, related.representatives, related.counter,
            congrArg (fun values => values.set root (.unenumerated (some handle) [])) related.values,
            related.obligations, related.recursionAncestry, related.expansionAncestry⟩
        · simp only [seen, ↓reduceIte] at observed ⊢
          obtain ⟨rfl, rfl⟩ := (EnumerationCorrectness.success_pure false result earlier after).mp observed
          exact ⟨flat, rfl, related⟩
      · simp only [boundary]
        exact EnumerationFlatReplay.pure_replays false

end MicroCFTA.SourceFlatPruningRecursion

import MicroCFTA.EnumerationFlatCore
import MicroCFTA.SourcePruningEnumerationTerminalPrefix

/-!
# Replay of successful earlier core traces

The old execution supplies actual successful intermediate states. The flat
execution returns one equal result and a related final state. This conditional
relation does not compare errors at insufficient old lookup bounds.
-/

namespace MicroCFTA.EnumerationFlatReplay

open EnumerationFlatState (Action Related)
open EnumerationCorrectness (Success)

attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Replay every successful earlier trace at its actual related input core. -/
def Replays (flat : Action Symbol Guard α) (earlier : EnumerationState.EnumerateM Symbol Guard α) : Prop :=
  ∀ left right value after, Related left right → Success earlier right value after →
    ∃ next, flat left = [.ok (value, next)] ∧ Related next after

/-- The same pure value retains the related complete input cores. -/
theorem pure_replays (value : α) :
    Replays (pure value : Action Symbol Guard α) (pure value) := by
  intro left right result after related observed
  obtain ⟨rfl, rfl⟩ := (EnumerationCorrectness.success_pure value result right after).mp observed
  exact ⟨left, rfl, related⟩

/-- Sequential replay follows the old execution's actual intermediate state. -/
theorem bind_replays (first : Action Symbol Guard α)
    (oldFirst : EnumerationState.EnumerateM Symbol Guard α)
    (next : α → Action Symbol Guard β) (oldNext : α → EnumerationState.EnumerateM Symbol Guard β)
    (initial : Replays first oldFirst) (following : ∀ value, Replays (next value) (oldNext value)) :
    Replays (first >>= next) (oldFirst >>= oldNext) := by
  intro left right value after related observed
  obtain ⟨middle, intermediate, head, tail⟩ :=
    (EnumerationCorrectness.success_bind oldFirst oldNext right value after).mp observed
  obtain ⟨nextLeft, firstDone, middleRelated⟩ := initial left right middle intermediate related head
  obtain ⟨finalLeft, lastDone, finalRelated⟩ :=
    following middle nextLeft intermediate value after middleRelated tail
  refine ⟨finalLeft, ?_, finalRelated⟩
  rw [EnumerationResultRelation.stateT_bind_rows]
  change (first left).flatMap _ = _
  rw [firstDone]
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using lastDone

/-- A successful old representative read has the same direct root and related final core. -/
theorem representative_replays (fuel uv : Nat) :
    Replays (EnumerationFlatState.representative uv) (EnumerationState.representative fuel uv) := by
  intro left right value after related observed
  obtain ⟨found, lookup, rfl, rfl⟩ :=
    (EnumerationSchedule.representative_success fuel uv right after value).mp observed
  obtain ⟨sameRoot, _size, retained⟩ := FlatUnionFind.findRoot_represents related.representatives lookup
  refine ⟨left, ?_, EnumerationFlatState.related_forests related related.valid retained⟩
  change [.ok (FlatUnionFind.root left.representatives uv, left)] = [.ok (found.representative, left)]
  rw [sameRoot]

/-- A successful old union follows the same requested raw variables. -/
theorem union_replays (fuel left right : Nat) :
    Replays (EnumerationFlatState.unionVariables left right) (EnumerationState.unionVariables fuel left right) := by
  intro flat earlier value after related observed
  cases value
  obtain ⟨forest, done, rfl⟩ :=
    (EnumerationSchedule.unionVariables_success fuel left right earlier after).mp observed
  exact ⟨{flat with representatives := FlatUnionFind.union flat.representatives left right}, rfl,
    EnumerationFlatState.related_forests related
      (FlatUnionFind.union_valid related.valid left right)
      (FlatUnionFind.union_represents related.valid related.representatives done)⟩

/-- Ordered mapping replays the same inputs and returned values. -/
theorem mapM_replays (flat : α → Action Symbol Guard β)
    (earlier : α → EnumerationState.EnumerateM Symbol Guard β)
    (each : ∀ input, Replays (flat input) (earlier input)) (inputs : List α) :
    Replays (inputs.mapM flat) (inputs.mapM earlier) := by
  induction inputs with
  | nil => exact pure_replays []
  | cons input rest ih =>
      rw [List.mapM_cons, List.mapM_cons]
      exact bind_replays _ _ _ _ (each input) fun head =>
        bind_replays _ _ _ _ ih fun tail => pure_replays (head :: tail)

/-- An ordered effect loop replays every operation before its continuation. -/
theorem forM_replays (flat : α → Action Symbol Guard PUnit)
    (earlier : α → EnumerationState.EnumerateM Symbol Guard PUnit)
    (each : ∀ input, Replays (flat input) (earlier input)) (inputs : List α) :
    Replays (inputs.forM flat) (inputs.forM earlier) := by
  induction inputs with
  | nil => exact pure_replays ()
  | cons input rest ih =>
      rw [List.forM_cons, List.forM_cons]
      exact bind_replays _ _ _ _ (each input) fun _ => ih

end MicroCFTA.EnumerationFlatReplay

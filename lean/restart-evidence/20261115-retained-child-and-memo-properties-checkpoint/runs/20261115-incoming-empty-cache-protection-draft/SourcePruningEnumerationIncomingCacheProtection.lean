import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
import MicroCFTA.SourcePruningEnumerationIsolatedPending
import MicroCFTA.SourcePruningEnumerationNativeReferences
import MicroCFTA.EnumerationDriver

/-!
# Protection through an actual empty incoming cache adaptation

The adapter writes an empty native sentinel at its actual target.
It appends the supplied references to the stored bucket.
The write retains the read forest and every other stored value.
A separate isolated class remains protected when the supplied inputs avoid it.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationReferences
open EnumerationDischargeHistory InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

set_option autoImplicit false

/-- Actual empty adaptation identifies the stored bucket and the complete sentinel write. -/
theorem adapt_empty_core
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (k target : Nat) (incomingScs : List Suspended) (before after : Cached) (read : Core)
    (adapted : adapt heap k target incomingScs before read [] = some after) :
    ∃ oldNode oldScs,
      read.values[target]? = some (.unenumerated oldNode oldScs) ∧
      after.core = {read with
        values := read.values.set target (.unenumerated (some 0) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = target then
          (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
          else read.recursionAncestry other} := by
  cases present : read.values[target]? with
  | none => simp [adapt, present] at adapted
  | some slot =>
    cases slot with
    | eliminated => simp [adapt, present] at adapted
    | enumerated fragment => simp [adapt, present] at adapted
    | unenumerated oldNode oldScs =>
      simp only [adapt, present, Option.map_eq_some_iff] at adapted
      obtain ⟨cached, _written, rfl⟩ := adapted
      exact ⟨oldNode, oldScs, present, rfl⟩

/-- The actual empty write protects the complete excluded class without a future premise. -/
theorem adapt_empty_protected_isolated
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (k target : Nat) (incomingScs : List Suspended) (before after : Cached) (read : Core)
    (held heldHandle : Nat)
    (isolated : IsolatedPending held heldHandle read)
    (different : target ≠ held)
    (inputs : Avoids read.representatives held incomingScs)
    (adapted : adapt heap k target incomingScs before read [] = some after) :
    EnumerationDriver.Protected held read after.core ∧
      IsolatedPending held heldHandle after.core := by
  obtain ⟨oldNode, oldScs, stored, shape⟩ :=
    adapt_empty_core heap k target incomingScs before after read adapted
  have forest : after.core.representatives = read.representatives := by rw [shape]
  have value : after.core.values[held]? = read.values[held]? := by
    rw [shape]
    exact List.getElem?_set_ne different
  have protected : EnumerationDriver.Protected held read after.core :=
    ⟨value, by simpa only [forest] using isolated.root, fun other => by rw [forest]⟩
  have allowed : ReferencesAllowed
      (fun uv => ¬UnionFind.SameClass read.representatives held uv) after.core :=
    SourcePruningEnumerationNativeReferences.incoming_written _ read after.core target 0
      oldNode incomingScs oldScs isolated.incoming inputs stored (by rw [shape])
  refine ⟨protected, ⟨protected.root, protected.value.trans isolated.stored, ?_⟩⟩
  intro slot member sc listed related
  exact allowed slot member sc listed (by simpa only [forest] using related)

/-- Every retained adaptation is an empty write or an exact successful singleton. -/
theorem adapt_retained_shape
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (k target : Nat) (incomingScs : List Suspended) (before after : Cached)
    (read : Core) (raw : Raw)
    (adapted : adapt heap k target incomingScs before read raw = some after) :
    raw = [] ∨ ∃ returned, raw = [.ok ((), returned)] ∧ after.core = returned := by
  cases raw with
  | nil => exact Or.inl rfl
  | cons row rest =>
    cases row with
    | error failure => simp [adapt] at adapted
    | ok pair =>
      rcases pair with ⟨⟨⟩, returned⟩
      cases rest with
      | nil =>
        exact Or.inr ⟨returned, rfl,
          adapt_singleton_core heap k target incomingScs before after read returned adapted⟩
      | cons second tail => simp [adapt] at adapted

end MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

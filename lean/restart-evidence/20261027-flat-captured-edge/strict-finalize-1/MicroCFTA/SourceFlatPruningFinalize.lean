import MicroCFTA.SourceFlatPruningCompletedIndex
import MicroCFTA.SourcePruningEnumerationFinalize

/-!
# Captured-slot finalization with direct-parent forests

Finalization clears expansion ancestry and reads the current raw captured slot.
It removes that slot's actual waiting references before storing the fragment.
-/

namespace MicroCFTA.SourceFlatPruningFinalize

open EnumerationState EnumerationSchedule EnumerationFlatCached
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Reset ancestry and replace the captured raw slot with the completed fragment. -/
def run (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (target : Nat) (fragment : Fragments.Fragment Symbol)
    (before : Cached Symbol EnumGuard) : Option (Cached Symbol EnumGuard) :=
  let reset := frame {before.core with expansionAncestry := []} before
  (reset.core.values[target]?).bind fun old =>
    EnumerationFlatNativeIndex.write heap target (.enumerated fragment) [] (references old) reset

private theorem reset_related (related : Related flat earlier) :
    Related (frame {flat.core with expansionAncestry := []} flat)
      (EnumerationExpandableIndex.frame {earlier.core with expansionAncestry := []} earlier) := by
  refine frame_related related ?_
  exact ⟨related.core.valid, related.core.representatives, related.core.counter,
    related.core.values, related.core.obligations, related.core.recursionAncestry, rfl⟩

/-- A completed old finalization supplies the actual related flat endpoint at the same heap. -/
theorem run_completed (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (completed : SourcePruningEnumerationFinalize.run heap fuel target fragment earlier = some after) :
    ∃ next, run heap target fragment flat = some next ∧ Related next after := by
  unfold SourcePruningEnumerationFinalize.run at completed
  simp only [EnumerationExpandableIndex.frame] at completed
  cases stored : earlier.core.values[target]? with
  | none =>
      simp only [stored, Option.bind_none] at completed
      cases completed
  | some old =>
      simp only [stored, Option.bind_some] at completed
      obtain ⟨next, actual, caches⟩ := SourceFlatPruningCompletedIndex.write_related
        (reset_related related) heap fuel target (.enumerated fragment) [] (references old) completed
      refine ⟨next, ?_, caches⟩
      simpa only [run, frame, related.core.values, stored, Option.bind_some] using actual

/-- The same raw-slot observation derives adequate old waiting-count bounds. -/
theorem run_stable (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (target : Nat) (fragment : Fragments.Fragment Symbol) :
    ∃ fuel, ∀ extra, EnumerationFlatNativeIndex.WritesRelated (run heap target fragment flat)
      (SourcePruningEnumerationFinalize.run heap (fuel + extra) target fragment earlier) := by
  cases stored : earlier.core.values[target]? with
  | none =>
      refine ⟨0, fun _ => ?_⟩
      simp only [run, SourcePruningEnumerationFinalize.run, frame, EnumerationExpandableIndex.frame,
        related.core.values, stored, Option.bind_none, EnumerationFlatNativeIndex.WritesRelated]
      trivial
  | some old =>
      obtain ⟨fuel, stable⟩ := EnumerationFlatNativeIndex.write_stable (reset_related related)
        heap target (.enumerated fragment) [] (references old)
      refine ⟨fuel, fun extra => ?_⟩
      simpa only [run, SourcePruningEnumerationFinalize.run, frame, EnumerationExpandableIndex.frame,
        related.core.values, stored, Option.bind_some] using stable extra

end MicroCFTA.SourceFlatPruningFinalize

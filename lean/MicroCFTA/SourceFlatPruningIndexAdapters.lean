import MicroCFTA.EnumerationFlatNativeIndex
import MicroCFTA.SourceFlatPruningCompletedIndex
import MicroCFTA.SourcePruningEnumerationParkedRestart
import MicroCFTA.SourcePruningEnumerationNarrowAdapter

/-!
# Native indexes after actual recursion and narrowing actions

The adapters rebuild indexes at the observed forest. They retain the actual
observed core separately from the synthetic index write's returned core.
-/

namespace MicroCFTA.SourceFlatPruningIndexAdapters

open EnumerationState EnumerationFlatCached EnumerationFlatNativeIndex
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Remove the original bucket and rebuild its flag at the actual checked forest. -/
def parked (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv handle : Nat) (scs : List Suspended) (before : Cached Symbol EnumGuard)
    (checked : EnumerationFlatState.State Symbol EnumGuard) : Option (Cached Symbol EnumGuard) :=
  (write heap uv (.unenumerated (some handle) []) [] scs (frame checked before)).map (frame checked)

/-- Attach unchanged or rebuilt indexes to the actual narrowing endpoint. -/
def narrowed (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv oldHandle newHandle : Nat) (scs : List Suspended) (before : Cached Symbol EnumGuard)
    (observed : EnumerationFlatState.State Symbol EnumGuard) : Option (Cached Symbol EnumGuard) :=
  if newHandle = oldHandle then some (frame observed before)
  else (write heap uv (.unenumerated (some newHandle) scs) scs scs
    (frame observed before)).map (frame observed)

/-- The parked cache retains the actual observed core. -/
theorem parked_core (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv handle : Nat) (scs : List Suspended) (before after : Cached Symbol EnumGuard)
    (checked : EnumerationFlatState.State Symbol EnumGuard)
    (completed : parked heap uv handle scs before checked = some after) : after.core = checked := by
  obtain ⟨written, _indexed, final⟩ := Option.map_eq_some_iff.mp completed
  subst after
  rfl

/-- The narrowing cache retains the actual observed core on both handle branches. -/
theorem narrowed_core (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv oldHandle newHandle : Nat) (scs : List Suspended) (before after : Cached Symbol EnumGuard)
    (observed : EnumerationFlatState.State Symbol EnumGuard)
    (completed : narrowed heap uv oldHandle newHandle scs before observed = some after) : after.core = observed := by
  unfold narrowed at completed
  split at completed
  · cases completed
    rfl
  · obtain ⟨written, _indexed, final⟩ := Option.map_eq_some_iff.mp completed
    subst after
    rfl

private theorem frame_options (cores : EnumerationFlatState.Related flatCore earlierCore)
    (writes : WritesRelated flat earlier) :
    WritesRelated (flat.map (frame flatCore)) (earlier.map (EnumerationExpandableIndex.frame earlierCore)) := by
  cases flat with
  | none => cases earlier <;> exact writes
  | some flat =>
      cases earlier with
      | none => exact writes
      | some earlier => exact frame_related writes cores

/-- Related checked cores derive adequate old counts without a future parked-cache premise. -/
theorem parked_stable (related : Related flat earlier)
    (checked : EnumerationFlatState.Related flatChecked earlierChecked)
    (heap : InternedConstructorTemplates.State Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (uv handle : Nat) (scs : List Suspended) :
    ∃ fuel, ∀ extra, WritesRelated (parked heap uv handle scs flat flatChecked)
      (SourcePruningEnumerationParkedRestart.adapt heap (fuel + extra) uv handle scs earlier earlierChecked) := by
  obtain ⟨fuel, stable⟩ := write_stable (frame_related related checked) heap uv
    (.unenumerated (some handle) []) [] scs
  exact ⟨fuel, fun extra => frame_options checked (stable extra)⟩

/-- Related narrowing endpoints derive both count folds at the same native heap. -/
theorem narrowed_stable (related : Related flat earlier)
    (observed : EnumerationFlatState.Related flatObserved earlierObserved)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv oldHandle newHandle : Nat) (scs : List Suspended) :
    ∃ fuel, ∀ extra, WritesRelated (narrowed heap uv oldHandle newHandle scs flat flatObserved)
      (SourcePruningEnumerationNarrowAdapter.adapt heap (fuel + extra) uv oldHandle newHandle scs
        earlier earlierObserved) := by
  by_cases same : newHandle = oldHandle
  · exact ⟨0, fun _ => by
      simpa only [narrowed, SourcePruningEnumerationNarrowAdapter.adapt, same, ↓reduceIte,
        WritesRelated] using frame_related related observed⟩
  · obtain ⟨fuel, stable⟩ := write_stable (frame_related related observed) heap uv
      (.unenumerated (some newHandle) scs) scs scs
    refine ⟨fuel, fun extra => ?_⟩
    simpa only [narrowed, SourcePruningEnumerationNarrowAdapter.adapt, same, ↓reduceIte] using
      frame_options observed (stable extra)

/-- A completed old parked adapter supplies the related flat cache at the same observation. -/
theorem parked_completed (related : Related flat earlier)
    (checked : EnumerationFlatState.Related flatChecked earlierChecked)
    (heap : InternedConstructorTemplates.State Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (fuel uv handle : Nat) (scs : List Suspended)
    (completed : SourcePruningEnumerationParkedRestart.adapt heap fuel uv handle scs earlier earlierChecked = some after) :
    ∃ next, parked heap uv handle scs flat flatChecked = some next ∧ Related next after := by
  obtain ⟨written, observed, final⟩ := Option.map_eq_some_iff.mp completed
  obtain ⟨flatWritten, flatObserved, states⟩ := SourceFlatPruningCompletedIndex.write_related
    (frame_related related checked) heap fuel uv (.unenumerated (some handle) []) [] scs observed
  refine ⟨frame flatChecked flatWritten, ?_, ?_⟩
  · simp only [parked, flatObserved, Option.map_some]
  · subst after
    exact frame_related states checked

/-- A completed old narrowing adapter supplies the related actual flat endpoint. -/
theorem narrowed_completed (related : Related flat earlier)
    (observed : EnumerationFlatState.Related flatObserved earlierObserved)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (completed : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle scs
      earlier earlierObserved = some after) :
    ∃ next, narrowed heap uv oldHandle newHandle scs flat flatObserved = some next ∧ Related next after := by
  by_cases same : newHandle = oldHandle
  · simp only [SourcePruningEnumerationNarrowAdapter.adapt, same, ↓reduceIte, Option.some.injEq] at completed
    refine ⟨frame flatObserved flat, ?_, ?_⟩
    · simp only [narrowed, same, ↓reduceIte]
    · rw [← completed]
      exact frame_related related observed
  · simp only [SourcePruningEnumerationNarrowAdapter.adapt, same, ↓reduceIte] at completed
    obtain ⟨written, indexed, final⟩ := Option.map_eq_some_iff.mp completed
    obtain ⟨flatWritten, flatIndexed, states⟩ := SourceFlatPruningCompletedIndex.write_related
      (frame_related related observed) heap fuel uv (.unenumerated (some newHandle) scs) scs scs indexed
    refine ⟨frame flatObserved flatWritten, ?_, ?_⟩
    · simp only [narrowed, same, ↓reduceIte, flatIndexed, Option.map_some]
    · subst after
      exact frame_related states observed

end MicroCFTA.SourceFlatPruningIndexAdapters

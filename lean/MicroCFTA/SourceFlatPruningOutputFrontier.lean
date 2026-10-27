import MicroCFTA.SourceFlatPruningRestart
import MicroCFTA.EnumerationFlatNativeIndex
import MicroCFTA.SourcePruningEnumerationRendering

/-!
# Exact restart decisions and the remaining native pending frontier

Done means that the native candidate list is empty.
Recursive boundaries can remain pending with an empty suspended bucket.
The rendering discharge condition is a separate property.
-/

namespace MicroCFTA.SourceFlatPruningOutputFrontier

open EnumerationState SourcePruningRecordTypes SourcePruningEnumerationNodes
open SourceFlatPruningRestart
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
variable {Typing NativeGuard : Type}

private theorem pick_done (preference : List Nat → Option Nat) (offered : Option (List Nat)) :
    pickNext preference offered = .done ↔ offered = none := by
  cases offered with
  | none => simp [pickNext]
  | some offered =>
      cases offered with
      | nil => simp [pickNext]
      | cons first rest =>
          cases chosen : preference (first :: rest) with
          | none => simp [pickNext, chosen]
          | some uv =>
              by_cases member : uv ∈ first :: rest <;> simp [pickNext, chosen, member]

private theorem pick_stuck (preference : List Nat → Option Nat) (offered : List Nat) :
    pickNext preference (some offered) = .stuck ↔ offered = [] := by
  cases offered with
  | nil => simp [pickNext]
  | cons first rest =>
      cases chosen : preference (first :: rest) with
      | none => simp [pickNext, chosen]
      | some uv =>
          by_cases member : uv ∈ first :: rest <;> simp [pickNext, chosen, member]

/-- Preference cannot turn a nonempty candidate list into done. -/
theorem next_done_iff (preference : List Nat → Option Nat) (before : Cached) :
    next preference before = .done ↔ candidates before = [] := by
  unfold next
  rw [pick_done]
  by_cases empty : candidates before = [] <;> simp [empty]

/-- Stuck retains candidates but has no unblocked candidate. -/
theorem next_stuck_iff (preference : List Nat → Option Nat) (before : Cached) :
    next preference before = .stuck ↔ candidates before ≠ [] ∧
      (candidates before).filter (fun uv => (before.waiting uv).isNone) = [] := by
  unfold next
  by_cases empty : candidates before = []
  · simp [empty, pickNext]
  · simp [empty, pick_stuck]

/-- A stop rule checks every candidate, including each blocked candidate. -/
theorem decision_none_iff (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached) :
    decision stop order metadata before = none ↔
      ∃ rule, stop = some rule ∧ candidates before ≠ [] ∧
        ∀ uv ∈ candidates before, rule metadata uv = true := by
  cases stop with
  | none => simp [decision]
  | some rule => simp [decision]

/-- Empty candidates produce done for every stop rule and preference. -/
theorem decision_done_iff (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached) :
    decision stop order metadata before = some .done ↔ candidates before = [] := by
  cases stop with
  | none => simpa [decision] using next_done_iff (order metadata) before
  | some rule =>
      by_cases empty : candidates before = []
      · simp [decision, empty, next_done_iff]
      · simp only [decision]
        split
        · simp [empty]
        · simpa only [Option.some.injEq] using next_done_iff (order metadata) before

/-- Stuck is distinct from both an accepted stop and done. -/
theorem decision_stuck_iff (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached) :
    decision stop order metadata before = some .stuck ↔
      decision stop order metadata before ≠ none ∧ candidates before ≠ [] ∧
        (candidates before).filter (fun uv => (before.waiting uv).isNone) = [] := by
  cases stop with
  | none => simpa [decision] using next_stuck_iff (order metadata) before
  | some rule =>
      simp only [decision]
      split
      · simp
      · simpa using next_stuck_iff (order metadata) before

/-- An empty candidate list fixes every allocated expandable flag to false. -/
theorem candidates_nil_iff (before : Cached) :
    candidates before = [] ↔ ∀ uv, uv < before.core.counter → before.expandable uv = false := by
  simp [candidates, List.filter_eq_nil_iff]

/-- A decoded native pending value is not a candidate exactly at recursive truncation. -/
theorem pending_false_iff
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (handle : Nat) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (scs : List Suspended) (decoded : lookupNode heap handle = some value) :
    SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated (some handle) scs) = some false ↔
      MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = [] := by
  simp [SourcePruningEnumerationNativeIndex.candidate, decoded]

/-- The genuine native invariant classifies every remaining graph-bearing pending slot. -/
theorem candidates_nil_iff_native_frontier
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : Cached) (earlier : EnumerationExpandableIndex.Cached Symbol Constraint)
    (related : EnumerationFlatCached.Related before earlier)
    (correct : EnumerationFlatNativeIndex.Correct heap before)
    (realized : SourcePruningEnumerationObservation.PendingRealized heap earlier.core) :
    candidates before = [] ↔
      ∀ (uv handle : Nat) (scs : List Suspended), before.core.values[uv]? = some (.unenumerated (some handle) scs) →
        ∃ value, lookupNode heap handle = some value ∧
          InternedProbeProvenance.Available heap value ∧ value.free = [] ∧
          MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = [] := by
  constructor
  · intro empty uv handle scs stored
    have inside : uv < before.core.counter := by
      rw [correct.aligned]
      exact (List.getElem?_eq_some_iff.mp stored).1
    have flag := (candidates_nil_iff before).mp empty uv inside
    have classified := correct.expandable uv
    rw [stored, Option.getD_some, flag] at classified
    obtain ⟨value, decoded, available, closed⟩ := realized uv handle scs
      (by simpa only [related.core.values] using stored)
    obtain ⟨recursive, noScs⟩ := (pending_false_iff heap handle value scs decoded).mp classified
    exact ⟨value, decoded, available, closed, recursive, noScs⟩
  · intro frontier
    apply (candidates_nil_iff before).mpr
    intro uv inside
    have bound : uv < before.core.values.length := by rw [← correct.aligned]; exact inside
    have stored : before.core.values[uv]? = some before.core.values[uv] :=
      List.getElem?_eq_getElem bound
    have classified := correct.expandable uv
    rw [stored, Option.getD_some] at classified
    cases valueEq : before.core.values[uv] with
    | enumerated fragment | eliminated =>
        simpa only [valueEq, SourcePruningEnumerationNativeIndex.candidate, Option.some.injEq]
          using classified.symm
    | unenumerated node scs =>
        cases node with
        | none =>
            simpa only [valueEq, SourcePruningEnumerationNativeIndex.candidate, Option.some.injEq]
              using classified.symm
        | some handle =>
            obtain ⟨value, decoded, _available, _closed, recursive, noScs⟩ :=
              frontier uv handle scs (by simpa only [valueEq] using stored)
            have noCandidate := (pending_false_iff heap handle value scs decoded).mpr ⟨recursive, noScs⟩
            rw [valueEq, noCandidate] at classified
            exact (Option.some.inj classified).symm

/-- Discharge additionally removes native pending handles and pure pending constraints. -/
theorem discharged_iff (before : Cached)
    (earlier : EnumerationExpandableIndex.Cached Symbol Constraint)
    (related : EnumerationFlatCached.Related before earlier) :
    SourcePruningEnumerationRendering.Discharged earlier.core ↔
      (∀ (uv handle : Nat) (scs : List Suspended), before.core.values[uv]? ≠ some (.unenumerated (some handle) scs)) ∧
      (∀ (uv : Nat) (scs : List Suspended), before.core.values[uv]? = some (.unenumerated none scs) → scs = []) := by
  constructor
  · intro discharged
    constructor
    · intro uv handle scs stored
      have impossible := discharged uv (some handle) scs
        (by simpa only [related.core.values] using stored)
      cases impossible.1
    · intro uv scs stored
      exact (discharged uv none scs (by simpa only [related.core.values] using stored)).2
  · rintro ⟨noHandle, noConstraints⟩ uv node scs stored
    have flatStored : before.core.values[uv]? = some (.unenumerated node scs) := by
      simpa only [related.core.values] using stored
    cases node with
    | none => exact ⟨rfl, noConstraints uv scs flatStored⟩
    | some handle => exact False.elim (noHandle uv handle scs flatStored)

/-- An actual available recursive boundary yields done while its initial slot is not discharged. -/
theorem recursive_initial_counterexample
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (handle : Nat) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (decoded : lookupNode heap handle = some value)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (recursive : MergedOrdinaryHeight.recursiveBoundary value = true)
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing) :
    ∃ before : Cached, ∃ earlier : EnumerationExpandableIndex.Cached Symbol Constraint,
      EnumerationFlatCached.Related before earlier ∧
      EnumerationFlatNativeIndex.Correct heap before ∧
      SourcePruningEnumerationObservation.PendingRealized heap earlier.core ∧
      decision none order metadata before = some .done ∧
      ¬ SourcePruningEnumerationRendering.Discharged earlier.core := by
  let before : Cached := ⟨EnumerationFlatState.initial handle, fun _ => false, fun _ => none⟩
  let earlier : EnumerationExpandableIndex.Cached Symbol Constraint :=
    ⟨EnumerationState.initial handle, fun _ => false, fun _ => none⟩
  refine ⟨before, earlier, ⟨EnumerationFlatState.initial_related handle, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩
    · intro uv
      cases uv with
      | zero => simp [before, EnumerationFlatState.initial,
          SourcePruningEnumerationNativeIndex.candidate, decoded, recursive]
      | succ uv => simp [before, EnumerationFlatState.initial,
          SourcePruningEnumerationNativeIndex.candidate]
    · intro uv
      simp [before, EnumerationFlatState.initial,
        EnumerationCanonicalWaiting.canonicalValue,
        EnumerationWaitingIndex.total, EnumerationWaitingIndex.occurrences,
        EnumerationWaitingIndex.encode, EnumerationSchedule.references]
  · intro uv storedHandle scs stored
    cases uv with
    | zero =>
        simp only [earlier, EnumerationState.initial, List.getElem?_cons_zero,
          Option.some.injEq, UVarValue.unenumerated.injEq, Option.some.injEq] at stored
        obtain ⟨rfl, rfl⟩ := stored
        exact ⟨value, decoded, available, closed⟩
    | succ uv => simp [earlier, EnumerationState.initial] at stored
  · apply (decision_done_iff none order metadata before).mpr
    simp [candidates, before, EnumerationFlatState.initial]
  · intro discharged
    have impossible := discharged 0 (some handle) [] (by rfl)
    cases impossible.1

end MicroCFTA.SourceFlatPruningOutputFrontier

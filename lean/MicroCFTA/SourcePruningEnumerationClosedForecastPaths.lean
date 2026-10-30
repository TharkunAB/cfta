import MicroCFTA.SourcePruningEnumerationPreparedReservation
import MicroCFTA.SourcePruningEnumerationForecastPathDomain
import MicroCFTA.SourceCurrentNativeClosedGuardAlphabet

/-!
# Original path carriers for both recursive guard forecasts

Every forecast guard stays in the same closed original alphabet.
The original finite carrier supplies paths at every recursive capacity.
-/
namespace MicroCFTA.SourcePruningEnumerationClosedForecastPaths
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationPathTransport (ProjectionPaths)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State SourcePruningTemplates.Symbol Constraint
local notation "Closed" => SourceCurrentNativeClosedGuardAlphabet.Closed
local notation "originalAlphabet" => SourceCurrentNativeClosedGuardAlphabet.originalAlphabet

private theorem guard_advance_subset (alphabet : List Constraint) (closed : Closed alphabet)
    (guards : List Constraint) (included : guards ⊆ alphabet) (count : Nat) :
    SourceCurrentNativeGuardAlphabet.advance guards count ⊆ alphabet := by
  induction count generalizing guards with
  | zero => exact included
  | succ count ih =>
      apply ih
      intro guard member
      exact SourceCurrentNativeClosedGuardAlphabet.step_subset alphabet closed
        (SourceCurrentNativeGuardAlphabet.step_mono included member)

private theorem incoming_advance_subset (alphabet : List Constraint) (closed : Closed alphabet)
    (seed : Seed) (included : seed.1 ⊆ alphabet) (count : Nat) :
    (SourcePruningEnumerationIncomingReservation.advance seed count).1 ⊆ alphabet := by
  induction count generalizing seed with
  | zero => exact included
  | succ count ih =>
      apply ih
      exact guard_advance_subset alphabet closed seed.1 included _

private theorem after_head_subset (alphabet : List Constraint) (closed : Closed alphabet)
    (seed : Seed) (included : seed.1 ⊆ alphabet) (inherited : Nat) :
    (SourcePruningEnumerationRecursiveReservation.afterHead seed inherited).1 ⊆ alphabet :=
  incoming_advance_subset alphabet closed seed included _

private theorem iterate_subset (alphabet : List Constraint) (next : Seed → Seed)
    (preserves : ∀ seed, seed.1 ⊆ alphabet → (next seed).1 ⊆ alphabet)
    (seed : Seed) (included : seed.1 ⊆ alphabet) (count : Nat) :
    (SourcePruningEnumerationFiniteReservation.iterate next seed count).1 ⊆ alphabet := by
  induction count generalizing seed with
  | zero => exact included
  | succ count ih => exact ih (next seed) (preserves seed included)

attribute [local irreducible] SourcePruningEnumerationFiniteReservation.iterate
attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHead
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
attribute [local irreducible] SourcePruningEnumerationSelectedValueCaller.normalizationProfile

/-- Every native recursive forecast remains inside the same closed guard alphabet. -/
theorem native_final_subset (alphabet : List Constraint) (closed : Closed alphabet)
    (depth : Nat) (seed : Seed) (ceiling : Nat) (included : seed.1 ⊆ alphabet) :
    (SourcePruningEnumerationFiniteReservation.final depth seed ceiling).1 ⊆ alphabet := by
  induction depth generalizing seed ceiling with
  | zero => exact included
  | succ depth ih =>
      rw [SourcePruningEnumerationFiniteReservation.final_succ]
      change (SourcePruningEnumerationFiniteReservation.iterate
        (fun current => SourcePruningEnumerationFiniteReservation.step depth current ceiling ceiling)
        (SourcePruningEnumerationExpansionAdmission.narrowSeed seed)
        (SourcePruningEnumerationFiniteReservation.rows seed)).1 ⊆ alphabet
      apply iterate_subset alphabet
      · intro current known
        exact ih (SourcePruningEnumerationRecursiveReservation.afterHead current ceiling)
          (SourcePruningEnumerationRecursiveReservation.massCeil current ceiling ceiling)
          (after_head_subset alphabet closed current known ceiling)
      · simpa only [SourcePruningEnumerationExpansionAdmission.narrowSeed] using included

/-- Every prepared recursive forecast remains inside the same closed guard alphabet. -/
theorem prepared_final_subset (alphabet : List Constraint) (closed : Closed alphabet)
    (depth : Nat) (seed : Seed) (ceiling : Nat) (included : seed.1 ⊆ alphabet) :
    (SourcePruningEnumerationPreparedReservation.final depth seed ceiling).1 ⊆ alphabet := by
  induction depth generalizing seed ceiling with
  | zero => exact included
  | succ depth ih =>
      rw [SourcePruningEnumerationPreparedReservation.final_succ]
      change (SourcePruningEnumerationFiniteReservation.iterate
        (fun current => SourcePruningEnumerationPreparedReservation.step depth current ceiling ceiling)
        (SourcePruningEnumerationPreparedReservation.preparedSeed seed)
        (SourcePruningEnumerationPreparedReservation.rows seed)).1 ⊆ alphabet
      apply iterate_subset alphabet
      · intro current known
        exact ih (SourcePruningEnumerationRecursiveReservation.afterHead current ceiling)
          (SourcePruningEnumerationRecursiveReservation.massCeil current ceiling ceiling)
          (after_head_subset alphabet closed current known ceiling)
      · simpa only [SourcePruningEnumerationPreparedReservation.preparedSeed] using included

/-- The original finite carrier supplies every native computed-forecast projected path. -/
theorem native_original_paths (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (initial : Core) (depth : Nat) (seed : Seed) (ceiling : Nat)
    (included : seed.1 ⊆ originalAlphabet literals) :
    ProjectionPaths (SourcePruningEnumerationFiniteReservation.final depth seed ceiling).1
      (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier
        (originalAlphabet literals) initial) := by
  have subset := native_final_subset (originalAlphabet literals)
    (SourceCurrentNativeClosedGuardAlphabet.original_closed literals normalized) depth seed ceiling included
  intro guard member tries residual projected trie chosen path represented
  exact SourcePruningEnumerationForecastPathDomain.projected_paths (originalAlphabet literals) initial
    guard (subset member) tries residual projected trie chosen path represented

/-- The same original finite carrier supplies every prepared computed-forecast projected path. -/
theorem prepared_original_paths (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (initial : Core) (depth : Nat) (seed : Seed) (ceiling : Nat)
    (included : seed.1 ⊆ originalAlphabet literals) :
    ProjectionPaths (SourcePruningEnumerationPreparedReservation.final depth seed ceiling).1
      (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier
        (originalAlphabet literals) initial) := by
  have subset := prepared_final_subset (originalAlphabet literals)
    (SourceCurrentNativeClosedGuardAlphabet.original_closed literals normalized) depth seed ceiling included
  intro guard member tries residual projected trie chosen path represented
  exact SourcePruningEnumerationForecastPathDomain.projected_paths (originalAlphabet literals) initial
    guard (subset member) tries residual projected trie chosen path represented

end MicroCFTA.SourcePruningEnumerationClosedForecastPaths

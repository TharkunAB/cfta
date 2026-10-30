import MicroCFTA.SourcePruningEnumerationClosedGuardForecast
import MicroCFTA.SourcePruningEnumerationFiniteReservation
import MicroCFTA.SourcePruningEnumerationPreparedReservation

/-!
# Original guard inventories through finite reservations

Every reservation stage stays in one closed original guard alphabet.
The result covers both ordinary and prepared reservation schedules.
It does not bound inherited payloads, storage, or recursive work.
-/
namespace MicroCFTA.SourcePruningEnumerationOriginalReservationAlphabet
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Seed" => List Guard × SourceCurrentAllocatedNativeResourceForecast.Profile
local notation "Closed" => SourceCurrentNativeClosedGuardAlphabet.Closed
local notation "alphabet" => SourceCurrentNativeClosedGuardAlphabet.originalAlphabet

/-- Native forecast extension stays in a fixed closed input inventory. -/
theorem native_advance_subset {original base : List Guard} (closed : Closed original)
    (included : base ⊆ original) (count : Nat) :
    SourceCurrentNativeGuardAlphabet.advance base count ⊆ original := by
  induction count generalizing base with
  | zero => exact included
  | succ count ih =>
      exact ih ((SourceCurrentNativeGuardAlphabet.step_mono included).trans
        (SourceCurrentNativeClosedGuardAlphabet.step_subset original closed))

/-- An actual incoming reservation step preserves the same inventory. -/
theorem incoming_step_subset {original : List Guard} (closed : Closed original)
    (seed : Seed) (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationIncomingReservation.step seed).1 ⊆ original := by
  exact native_advance_subset closed included _

/-- Every actual incoming reservation prefix uses that inventory. -/
theorem incoming_advance_subset {original : List Guard} (closed : Closed original)
    (seed : Seed) (count : Nat) (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationIncomingReservation.advance seed count).1 ⊆ original := by
  induction count generalizing seed with
  | zero => exact included
  | succ count ih => exact ih _ (incoming_step_subset closed seed included)

/-- The actual head reservation preserves the inventory for any count bound. -/
theorem afterHead_subset {original : List Guard} (closed : Closed original)
    (seed : Seed) (inherited : Nat) (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationRecursiveReservation.afterHead seed inherited).1 ⊆ original :=
  incoming_advance_subset closed seed _ included

attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHead
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile

/-- A finite iteration preserves an input-inventory invariant. -/
theorem iterate_subset {original : List Guard} (next : Seed → Seed)
    (preserves : ∀ seed, seed.1 ⊆ original → (next seed).1 ⊆ original)
    (seed : Seed) (count : Nat) (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationFiniteReservation.iterate next seed count).1 ⊆ original := by
  induction count generalizing seed with
  | zero => exact included
  | succ count ih => exact ih _ (preserves seed included)

/-- Every final finite reservation uses the same original inventory. -/
theorem final_subset {original : List Guard} (closed : Closed original)
    (depth : Nat) (seed : Seed) (ceiling : Nat) (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationFiniteReservation.final depth seed ceiling).1 ⊆ original := by
  induction depth generalizing seed ceiling with
  | zero => exact included
  | succ depth ih =>
      apply iterate_subset
      · intro current present
        exact ih _ _ (afterHead_subset closed current ceiling present)
      · change seed.1 ⊆ original
        exact included

/-- The actual paired step retains the inventory for all mass and length bounds. -/
theorem step_subset {original : List Guard} (closed : Closed original)
    (depth : Nat) (seed : Seed) (capturedMass inherited : Nat)
    (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationFiniteReservation.step depth seed capturedMass inherited).1 ⊆ original :=
  final_subset closed depth _ _ (afterHead_subset closed seed inherited included)

/-- Every original sibling stage stays in the same closed inventory. -/
theorem stage_subset {original : List Guard} (closed : Closed original)
    (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat)
    (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationFiniteReservation.stage depth seed capturedMass inherited count).1 ⊆ original :=
  iterate_subset _ (fun current present => step_subset closed depth current capturedMass inherited present)
    seed count included

/-- Original normalized literal caches determine one inventory for every stage. -/
theorem stage_original_subset (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat)
    (included : seed.1 ⊆ alphabet literals) :
    (SourcePruningEnumerationFiniteReservation.stage depth seed capturedMass inherited count).1 ⊆
      alphabet literals :=
  stage_subset (SourceCurrentNativeClosedGuardAlphabet.original_closed literals normalized)
    depth seed capturedMass inherited count included

/-- Prepared normalization changes the profile but retains the guard inventory. -/
theorem prepared_final_subset {original : List Guard} (closed : Closed original)
    (depth : Nat) (seed : Seed) (ceiling : Nat) (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationPreparedReservation.final depth seed ceiling).1 ⊆ original := by
  induction depth generalizing seed ceiling with
  | zero => exact included
  | succ depth ih =>
      apply iterate_subset
      · intro current present
        exact ih _ _ (afterHead_subset closed current ceiling present)
      · change seed.1 ⊆ original
        exact included

/-- The actual prepared paired step uses the same original inventory. -/
theorem prepared_step_subset {original : List Guard} (closed : Closed original)
    (depth : Nat) (seed : Seed) (capturedMass inherited : Nat)
    (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationPreparedReservation.step depth seed capturedMass inherited).1 ⊆ original :=
  prepared_final_subset closed depth _ _ (afterHead_subset closed seed inherited included)

/-- Every prepared sibling stage preserves the original closed inventory. -/
theorem prepared_stage_subset {original : List Guard} (closed : Closed original)
    (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat)
    (included : seed.1 ⊆ original) :
    (SourcePruningEnumerationPreparedReservation.stage depth seed capturedMass inherited count).1 ⊆ original :=
  iterate_subset _ (fun current present => prepared_step_subset closed depth current capturedMass inherited present)
    seed count included

/-- The same normalized original literals cover all prepared reservation stages. -/
theorem prepared_stage_original_subset (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat)
    (included : seed.1 ⊆ alphabet literals) :
    (SourcePruningEnumerationPreparedReservation.stage depth seed capturedMass inherited count).1 ⊆
      alphabet literals :=
  prepared_stage_subset (SourceCurrentNativeClosedGuardAlphabet.original_closed literals normalized)
    depth seed capturedMass inherited count included

end MicroCFTA.SourcePruningEnumerationOriginalReservationAlphabet

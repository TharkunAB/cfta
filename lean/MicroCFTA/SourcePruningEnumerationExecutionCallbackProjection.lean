import MicroCFTA.SourcePruningEnumerationFiniteReservation
import MicroCFTA.SourcePruningEnumerationPreparedReservation
import MicroCFTA.SourcePruningEnumerationPathTransport

/-!
# Computed callback forecast projections

Each callback uses the exact smaller forecast.
The outer stage or final forecast supplies its projection paths.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionCallbackProjection
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationPathTransport (ProjectionPaths)
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil

namespace Native

/-- The original finite sibling forecast supplies the exact callback projection. -/
theorem callback_projection_of_stage
    {P : EqualityTrie.Path → Prop} (depth : Nat) (seed : Seed)
    (capturedMass inherited index count : Nat) (inside : index < count)
    (projected : ProjectionPaths (SourcePruningEnumerationFiniteReservation.stage depth seed capturedMass inherited count).1 P) :
    ProjectionPaths
      (SourcePruningEnumerationFiniteReservation.final depth
        (afterHead (SourcePruningEnumerationFiniteReservation.stage depth seed capturedMass inherited index) inherited)
        (massCeil (SourcePruningEnumerationFiniteReservation.stage depth seed capturedMass inherited index) capturedMass inherited)).1 P := by
  intro guard member
  have stepMember : guard ∈
      (SourcePruningEnumerationFiniteReservation.step depth
        (SourcePruningEnumerationFiniteReservation.stage depth seed capturedMass inherited index) capturedMass inherited).1 := by
    simpa only [SourcePruningEnumerationFiniteReservation.step] using member
  have stageMember : guard ∈
      (SourcePruningEnumerationFiniteReservation.stage depth seed capturedMass inherited (index + 1)).1 := by
    rw [SourcePruningEnumerationFiniteReservation.stage_succ_right]
    exact stepMember
  have counts : index + 1 ≤ count := by omega
  exact projected guard ((SourcePruningEnumerationFiniteReservation.count_mono depth seed capturedMass inherited counts).2 stageMember)

/-- The original positive-depth forecast supplies each actual callback projection. -/
theorem callback_projection_of_final
    {P : EqualityTrie.Path → Prop} (depth : Nat) (seed : Seed) (ceiling index : Nat)
    (inside : index < SourcePruningEnumerationFiniteReservation.rows seed)
    (projected : ProjectionPaths (SourcePruningEnumerationFiniteReservation.final (depth + 1) seed ceiling).1 P) :
    ProjectionPaths
      (SourcePruningEnumerationFiniteReservation.final depth
        (afterHead (SourcePruningEnumerationFiniteReservation.stage depth (SourcePruningEnumerationExpansionAdmission.narrowSeed seed) ceiling ceiling index) ceiling)
        (massCeil (SourcePruningEnumerationFiniteReservation.stage depth (SourcePruningEnumerationExpansionAdmission.narrowSeed seed) ceiling ceiling index) ceiling ceiling)).1 P := by
  have stageProjected : ProjectionPaths
      (SourcePruningEnumerationFiniteReservation.stage depth (SourcePruningEnumerationExpansionAdmission.narrowSeed seed) ceiling ceiling (SourcePruningEnumerationFiniteReservation.rows seed)).1 P := by
    simpa only [SourcePruningEnumerationFiniteReservation.final_succ] using projected
  exact callback_projection_of_stage depth (SourcePruningEnumerationExpansionAdmission.narrowSeed seed) ceiling ceiling index
    (SourcePruningEnumerationFiniteReservation.rows seed) inside stageProjected

end Native

namespace Prepared

/-- The original finite sibling forecast supplies the exact callback projection. -/
theorem callback_projection_of_stage
    {P : EqualityTrie.Path → Prop} (depth : Nat) (seed : Seed)
    (capturedMass inherited index count : Nat) (inside : index < count)
    (projected : ProjectionPaths (SourcePruningEnumerationPreparedReservation.stage depth seed capturedMass inherited count).1 P) :
    ProjectionPaths
      (SourcePruningEnumerationPreparedReservation.final depth
        (afterHead (SourcePruningEnumerationPreparedReservation.stage depth seed capturedMass inherited index) inherited)
        (massCeil (SourcePruningEnumerationPreparedReservation.stage depth seed capturedMass inherited index) capturedMass inherited)).1 P := by
  intro guard member
  have stepMember : guard ∈
      (SourcePruningEnumerationPreparedReservation.step depth
        (SourcePruningEnumerationPreparedReservation.stage depth seed capturedMass inherited index) capturedMass inherited).1 := by
    simpa only [SourcePruningEnumerationPreparedReservation.step] using member
  have stageMember : guard ∈
      (SourcePruningEnumerationPreparedReservation.stage depth seed capturedMass inherited (index + 1)).1 := by
    rw [SourcePruningEnumerationPreparedReservation.stage_succ_right]
    exact stepMember
  have counts : index + 1 ≤ count := by omega
  exact projected guard ((SourcePruningEnumerationPreparedReservation.count_mono depth seed capturedMass inherited counts).2 stageMember)

/-- The original positive-depth forecast supplies each actual callback projection. -/
theorem callback_projection_of_final
    {P : EqualityTrie.Path → Prop} (depth : Nat) (seed : Seed) (ceiling index : Nat)
    (inside : index < SourcePruningEnumerationPreparedReservation.rows seed)
    (projected : ProjectionPaths (SourcePruningEnumerationPreparedReservation.final (depth + 1) seed ceiling).1 P) :
    ProjectionPaths
      (SourcePruningEnumerationPreparedReservation.final depth
        (afterHead (SourcePruningEnumerationPreparedReservation.stage depth (SourcePruningEnumerationPreparedReservation.preparedSeed seed) ceiling ceiling index) ceiling)
        (massCeil (SourcePruningEnumerationPreparedReservation.stage depth (SourcePruningEnumerationPreparedReservation.preparedSeed seed) ceiling ceiling index) ceiling ceiling)).1 P := by
  have stageProjected : ProjectionPaths
      (SourcePruningEnumerationPreparedReservation.stage depth (SourcePruningEnumerationPreparedReservation.preparedSeed seed) ceiling ceiling (SourcePruningEnumerationPreparedReservation.rows seed)).1 P := by
    simpa only [SourcePruningEnumerationPreparedReservation.final_succ] using projected
  exact callback_projection_of_stage depth (SourcePruningEnumerationPreparedReservation.preparedSeed seed) ceiling ceiling index
    (SourcePruningEnumerationPreparedReservation.rows seed) inside stageProjected

end Prepared

end MicroCFTA.SourcePruningEnumerationExecutionCallbackProjection

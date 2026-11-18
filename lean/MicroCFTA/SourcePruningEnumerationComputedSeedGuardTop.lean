import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation
import MicroCFTA.SourcePruningEnumerationSharedPreparedReservation
import MicroCFTA.SourceSynthesisCurrentGuardPoolPositivity

namespace MicroCFTA.SourcePruningEnumerationComputedSeedGuardTop
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
set_option autoImplicit false

theorem generated_query_forecast_top
    (initial : List Constraint) (profile : Profile)
    (initialTop : ∀ guard ∈ initial, guard.guard = .top) :
    ∀ guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast initial profile, guard.guard = .top
 := by
  intro guard member
  change guard ∈ SourceCurrentNativeGuardAlphabet.advance initial
    (SourceCurrentAllocatedNativeComputedBudget.instructionBound profile.nodes profile.edges profile.mass) at member
  exact (SourceSynthesisCurrentGuardPoolPositivity.native_guard_pool_advance_positive
    initial initialTop
    (SourceCurrentAllocatedNativeComputedBudget.instructionBound profile.nodes profile.edges profile.mass)
    guard member).1

theorem shared_incoming_step_top
    (seed : Seed) (initialTop : ∀ guard ∈ seed.1, guard.guard = .top) :
    ∀ guard ∈ (SourcePruningEnumerationSharedIncomingReservation.step seed).1, guard.guard = .top
 := by
  change ∀ guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast seed.1 seed.2, guard.guard = .top
  exact generated_query_forecast_top seed.1 seed.2 initialTop

theorem shared_incoming_advance_top
    (seed : Seed) (initialTop : ∀ guard ∈ seed.1, guard.guard = .top) (count : Nat) :
    ∀ guard ∈ (SourcePruningEnumerationSharedIncomingReservation.advance seed count).1, guard.guard = .top
 := by
  induction count generalizing seed with
  | zero => exact initialTop
  | succ count ih =>
      change ∀ guard ∈ (SourcePruningEnumerationSharedIncomingReservation.advance
        (SourcePruningEnumerationSharedIncomingReservation.step seed) count).1, guard.guard = .top
      exact ih (SourcePruningEnumerationSharedIncomingReservation.step seed)
        (shared_incoming_step_top seed initialTop)

theorem prepared_seed_top
    (seed : Seed) (initialTop : ∀ guard ∈ seed.1, guard.guard = .top) :
    ∀ guard ∈ (SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed).1, guard.guard = .top
 := by
  dsimp only [SourcePruningEnumerationSharedPreparedReservation.preparedSeed]
  exact initialTop

end MicroCFTA.SourcePruningEnumerationComputedSeedGuardTop

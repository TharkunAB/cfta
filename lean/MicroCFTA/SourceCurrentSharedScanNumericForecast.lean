import MicroCFTA.SourceCurrentGateFrameResources
import MicroCFTA.SourceCurrentSeededGuardForecast
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerResources

/-!
# Initial numeric schedules for the actual shared Scan

Each class reserves both gates, the first-seeded query, and the conjunction
memo. Early exits can use the same larger forecast. The original class
suffix receives the predicted profile and finite guard alphabet. The shared
memo uses that exact alphabet in its numeric shape forecast. Native room
stays explicit in each seeded reservation.
-/
namespace MicroCFTA.SourceCurrentSharedScanNumericForecast
open EqualityNormalize
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "gateProfile" => SourceCurrentGateFrameResources.forecast
local notation "seedProfile" => SourceCurrentConstrainedCapSeededForecast.finalProfile
local notation "seedAlphabet" => SourceCurrentSeededGuardForecast.finalAlphabet
local notation "memoProfile" => SourceCurrentAllocatedSharedConjunctionWorkerActual.forecast_with_alphabet


/-- The same fixed-alphabet memo forecast retains every initial profile component. -/
theorem memoProfile_ge (alphabet : List Guard) (budget : Nat) (profile : Profile) :
    Le profile (memoProfile alphabet budget profile) := by
  have retained := SourceCurrentConjunctionSharedFixedAlphabetNumeric.forecast_ge alphabet budget
    (SourceCurrentConstrainedCapTargetForecast.scalar profile)
  have scalarBound : SourceCurrentConstrainedCapTargetForecast.scalar profile ≤
      SourceCurrentConjunctionSharedFixedAlphabetNumeric.forecast alphabet budget
        (SourceCurrentConstrainedCapTargetForecast.scalar profile) :=
    Nat.le_trans (Nat.le_max_left _ _) retained
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile) scalarBound,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile) scalarBound,
    Nat.le_refl _, Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile) scalarBound⟩

/-- One class predicts every allocating branch before the original suffix. -/
noncomputable def classStep (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) :
    List Guard × Profile :=
  let secondary := gateProfile paths profile
  let seeded := gateProfile paths secondary
  let signed := paths.map (List.map Int.ofNat)
  let native := seedProfile count signed seeded
  let guards := seedAlphabet alphabet count signed seeded
  (guards, memoProfile guards budget native)

/-- Every original numeric component fits the complete class forecast. -/
theorem classStep_profile_ge (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) :
    Le profile (classStep budget count paths alphabet profile).2 := by
  have seeded : Le (gateProfile paths (gateProfile paths profile))
      (seedProfile count (paths.map (List.map Int.ofNat)) (gateProfile paths (gateProfile paths profile))) := by
    cases paths with
    | nil => exact Le.refl _
    | cons seed rest =>
        exact SourceCurrentConstrainedCapSeededForecast.fold_ge count (seed.map Int.ofNat)
          (rest.map (List.map Int.ofNat)) _
  exact (SourceCurrentGateFrameResources.forecast_ge paths profile).trans
    ((SourceCurrentGateFrameResources.forecast_ge paths _).trans
      (seeded.trans (memoProfile_ge _ _ _)))

/-- Every entry guard remains in the complete class forecast. -/
theorem classStep_alphabet_ge (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) :
    alphabet ⊆ (classStep budget count paths alphabet profile).1 :=
  SourceCurrentSeededGuardForecast.final_ge _ _ _ _

private theorem seeded_ge (count : Nat) (paths : Class) (profile : Profile) :
    Le profile (seedProfile count (paths.map (List.map Int.ofNat)) profile) := by
  cases paths with
  | nil => exact Le.refl _
  | cons seed rest =>
      exact SourceCurrentConstrainedCapSeededForecast.fold_ge count (seed.map Int.ofNat) (rest.map (List.map Int.ofNat)) profile

/-- A primary-only return fits the remaining reserved class stages. -/
theorem classStep_primary_ge (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) :
    Le (gateProfile paths profile) (classStep budget count paths alphabet profile).2 :=
  (SourceCurrentGateFrameResources.forecast_ge paths _).trans
    ((seeded_ge count paths _).trans (memoProfile_ge _ _ _))

/-- A secondary-only return fits the remaining reserved class stages. -/
theorem classStep_secondary_ge (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) :
    Le (gateProfile paths (gateProfile paths profile)) (classStep budget count paths alphabet profile).2 :=
  (seeded_ge count paths _).trans (memoProfile_ge _ _ _)

/-- The original ordered class list determines both final forecasts. -/
noncomputable def schedule (budget count : Nat) : Constraints → List Guard → Profile → List Guard × Profile
  | [], alphabet, profile => (alphabet, profile)
  | paths :: classes, alphabet, profile =>
      let next := classStep budget count paths alphabet profile
      schedule budget count classes next.1 next.2

/-- The complete schedule retains every initial numeric component. -/
theorem schedule_profile_ge (budget count : Nat) (classes : Constraints) (alphabet : List Guard) (profile : Profile) :
    Le profile (schedule budget count classes alphabet profile).2 := by
  induction classes generalizing alphabet profile with
  | nil => exact Le.refl _
  | cons paths classes ih => exact (classStep_profile_ge budget count paths alphabet profile).trans (ih _ _)

/-- The complete schedule retains every initial guard. -/
theorem schedule_alphabet_ge (budget count : Nat) (classes : Constraints) (alphabet : List Guard) (profile : Profile) :
    alphabet ⊆ (schedule budget count classes alphabet profile).1 := by
  induction classes generalizing alphabet profile with
  | nil => exact fun _ member => member
  | cons paths classes ih =>
      intro guard member
      exact ih _ _ (classStep_alphabet_ge budget count paths alphabet profile member)

/-- Each native reservation refers only to a pure predicted query entry. -/
noncomputable def Reserved (bits budget count : Nat) : Constraints → List Guard → Profile → Prop
  | [], _, _ => True
  | paths :: classes, alphabet, profile =>
      SourceCurrentConstrainedCapSeededForecast.SeededReserved bits count (paths.map (List.map Int.ofNat))
        (gateProfile paths (gateProfile paths profile)) ∧
      let next := classStep budget count paths alphabet profile
      Reserved bits budget count classes next.1 next.2

/-- One shared ceiling bounds every phase in the current class. -/
noncomputable def classFuel (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) : Nat :=
  let secondary := gateProfile paths profile
  let seeded := gateProfile paths secondary
  let signed := paths.map (List.map Int.ofNat)
  let native := seedProfile count signed seeded
  let guards := seedAlphabet alphabet count signed seeded
  max (SourceCurrentGateFrameResources.workerFuel paths profile)
    (max (SourceCurrentGateFrameResources.workerFuel paths secondary)
      (max (SourceCurrentConstrainedCapSeededForecast.fuel count signed seeded)
        (max (SourceCurrentAllocatedSharedConjunctionWorkerActual.projectionFuel guards budget native)
          (SourceCurrentAllocatedSharedConjunctionWorkerActual.readerFuel guards budget native))))

/-- The class ceiling covers both gates, all seeded phases, and both conjunction workers. -/
theorem classFuel_limits (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) :
    SourceCurrentGateFrameResources.workerFuel paths profile ≤ classFuel budget count paths alphabet profile ∧
    SourceCurrentGateFrameResources.workerFuel paths (gateProfile paths profile) ≤ classFuel budget count paths alphabet profile ∧
    SourceCurrentConstrainedCapSeededForecast.fuel count (paths.map (List.map Int.ofNat))
      (gateProfile paths (gateProfile paths profile)) ≤ classFuel budget count paths alphabet profile ∧
    SourceCurrentAllocatedSharedConjunctionWorkerActual.projectionFuel
      (classStep budget count paths alphabet profile).1 budget
      (seedProfile count (paths.map (List.map Int.ofNat)) (gateProfile paths (gateProfile paths profile))) ≤
          classFuel budget count paths alphabet profile ∧
    SourceCurrentAllocatedSharedConjunctionWorkerActual.readerFuel
      (classStep budget count paths alphabet profile).1 budget
      (seedProfile count (paths.map (List.map Int.ofNat)) (gateProfile paths (gateProfile paths profile))) ≤
          classFuel budget count paths alphabet profile := by
  dsimp only [classFuel, classStep]
  omega

/-- The original class suffix uses the same predicted profile and alphabet as its reservation. -/
noncomputable def fuel (budget count : Nat) : Constraints → List Guard → Profile → Nat
  | [], _, _ => 0
  | paths :: classes, alphabet, profile =>
      let next := classStep budget count paths alphabet profile
      max (classFuel budget count paths alphabet profile) (fuel budget count classes next.1 next.2)

end MicroCFTA.SourceCurrentSharedScanNumericForecast

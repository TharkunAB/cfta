import MicroCFTA.SourceCurrentGateFrameResources
import MicroCFTA.SourceCurrentSeededGuardForecast
import MicroCFTA.SourceCurrentConjunctionAlphabetBounds

/-!
# Initial numeric schedules for the complete current Scan

Each class reserves both gates, the first-seeded query, and the conjunction
memo. Early exits can use the same larger forecast. The original class
suffix receives the predicted profile and finite guard alphabet.
-/
namespace MicroCFTA.SourceCurrentScanNumericForecast
open EqualityNormalize
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "gateProfile" => SourceCurrentGateFrameResources.forecast
local notation "seedProfile" => SourceCurrentConstrainedCapSeededForecast.finalProfile
local notation "seedAlphabet" => SourceCurrentSeededGuardForecast.finalAlphabet
local notation "memoProfile" => SourceCurrentConjunctionAlphabetBounds.callerForecast

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
    | cons seed rest => exact SourceCurrentConstrainedCapSeededForecast.fold_ge count (seed.map Int.ofNat)
        (rest.map (List.map Int.ofNat)) _
  exact (SourceCurrentGateFrameResources.forecast_ge paths profile).trans
    ((SourceCurrentGateFrameResources.forecast_ge paths _).trans
      (seeded.trans (SourceCurrentConjunctionAlphabetBounds.callerForecast_ge _ _ _)))

/-- Every entry guard remains in the complete class forecast. -/
theorem classStep_alphabet_ge (budget count : Nat) (paths : Class) (alphabet : List Guard) (profile : Profile) :
    alphabet ⊆ (classStep budget count paths alphabet profile).1 :=
  SourceCurrentSeededGuardForecast.final_ge _ _ _ _

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
        (max (SourceCurrentConjunctionWorklistResources.workerFuel guards budget
          (SourceCurrentConstrainedCapTargetForecast.scalar native))
          (SourceCurrentConjunctionWorklistResources.readerFuel guards budget
            (SourceCurrentConstrainedCapTargetForecast.scalar native)))))

/-- The original class suffix uses the same predicted profile and alphabet as its reservation. -/
noncomputable def fuel (budget count : Nat) : Constraints → List Guard → Profile → Nat
  | [], _, _ => 0
  | paths :: classes, alphabet, profile =>
      let next := classStep budget count paths alphabet profile
      max (classFuel budget count paths alphabet profile) (fuel budget count classes next.1 next.2)

end MicroCFTA.SourceCurrentScanNumericForecast

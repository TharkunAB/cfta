import MicroCFTA.SourceCurrentScanNumericForecast
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
namespace MicroCFTA.ScanForecastCheck
open EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentScanNumericForecast
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
private def placeholders : List (Value Symbol Guard) := [.reference .depth, .empty]
private def firstPaths : Class := [[0, 0], [0, 1]]
private def lastPaths : Class := [[0], [1]]

/-- Exact stage order, reservations, and fuel retain the original two-class sequence. -/
theorem ordered_two_classes (bits budget : Nat) (alphabet : List Guard) (entry : Profile) :
    let first := classStep budget placeholders.length firstPaths alphabet entry
    let last := classStep budget placeholders.length lastPaths first.1 first.2
    (classStep budget placeholders.length firstPaths alphabet entry =
      let primary := SourceCurrentGateFrameResources.forecast firstPaths entry
      let secondary := SourceCurrentGateFrameResources.forecast firstPaths primary
      let signed := firstPaths.map (List.map Int.ofNat)
      let query := SourceCurrentConstrainedCapSeededForecast.finalProfile placeholders.length signed secondary
      let guards := SourceCurrentSeededGuardForecast.finalAlphabet alphabet placeholders.length signed secondary
      (guards, SourceCurrentConjunctionAlphabetBounds.callerForecast guards budget query)) ∧
    schedule budget placeholders.length [firstPaths, lastPaths] alphabet entry = last ∧
    (Reserved bits budget placeholders.length [firstPaths, lastPaths] alphabet entry ↔
      SourceCurrentConstrainedCapSeededForecast.SeededReserved bits placeholders.length
        (firstPaths.map (List.map Int.ofNat))
        (SourceCurrentGateFrameResources.forecast firstPaths (SourceCurrentGateFrameResources.forecast firstPaths entry)) ∧
      SourceCurrentConstrainedCapSeededForecast.SeededReserved bits placeholders.length
        (lastPaths.map (List.map Int.ofNat))
        (SourceCurrentGateFrameResources.forecast lastPaths (SourceCurrentGateFrameResources.forecast lastPaths first.2))) ∧
    fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry =
      max (classFuel budget placeholders.length firstPaths alphabet entry)
        (classFuel budget placeholders.length lastPaths first.1 first.2) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · constructor
    · intro reserved
      exact ⟨reserved.1, reserved.2.1⟩
    · intro reserved
      exact ⟨reserved.1, reserved.2, True.intro⟩
  · simp only [fuel, Nat.max_zero]

/-- Early exits and every component threshold below either class ceiling fit the same two-class fuel. -/
theorem padded_two_classes (budget : Nat) (alphabet : List Guard) (entry : Profile) :
    let first := classStep budget placeholders.length firstPaths alphabet entry
    let last := classStep budget placeholders.length lastPaths first.1 first.2
    Le (SourceCurrentGateFrameResources.forecast firstPaths entry) last.2 ∧
    Le (SourceCurrentGateFrameResources.forecast firstPaths (SourceCurrentGateFrameResources.forecast firstPaths entry)) last.2 ∧
    alphabet ⊆ last.1 ∧
    (∀ phase, phase ≤ classFuel budget placeholders.length firstPaths alphabet entry →
      phase ≤ fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry) ∧
    (∀ phase, phase ≤ classFuel budget placeholders.length lastPaths first.1 first.2 →
      phase ≤ fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry) := by
  let first := classStep budget placeholders.length firstPaths alphabet entry
  let last := classStep budget placeholders.length lastPaths first.1 first.2
  have tailProfile : Le first.2 last.2 := classStep_profile_ge budget placeholders.length lastPaths first.1 first.2
  have primaryFits := @Le.trans (SourceCurrentGateFrameResources.forecast firstPaths entry) first.2 last.2
    (classStep_primary_ge budget placeholders.length firstPaths alphabet entry) tailProfile
  have secondaryFits := @Le.trans
    (SourceCurrentGateFrameResources.forecast firstPaths (SourceCurrentGateFrameResources.forecast firstPaths entry))
    first.2 last.2 (classStep_secondary_ge budget placeholders.length firstPaths alphabet entry) tailProfile
  have guards := schedule_alphabet_ge budget placeholders.length [firstPaths, lastPaths] alphabet entry
  have firstFuel : classFuel budget placeholders.length firstPaths alphabet entry ≤
      fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry := by
    change _ ≤ max _ _
    exact Nat.le_max_left _ _
  have lastFuel : classFuel budget placeholders.length lastPaths first.1 first.2 ≤
      fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry := by
    change _ ≤ max _ (max _ 0)
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  exact ⟨primaryFits, secondaryFits, guards,
    fun _ lower => Nat.le_trans lower firstFuel, fun _ lower => Nat.le_trans lower lastFuel⟩
end MicroCFTA.ScanForecastCheck
#check @MicroCFTA.ScanForecastCheck.ordered_two_classes
#print axioms MicroCFTA.ScanForecastCheck.ordered_two_classes
#check @MicroCFTA.ScanForecastCheck.padded_two_classes
#print axioms MicroCFTA.ScanForecastCheck.padded_two_classes

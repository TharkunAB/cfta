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
private theorem ordered_stages (bits budget count : Nat) (firstPaths lastPaths : Class) (alphabet : List Guard) (entry : Profile) :
    let first := classStep budget count firstPaths alphabet entry
    let last := classStep budget count lastPaths first.1 first.2
    (classStep budget count firstPaths alphabet entry =
      let primary := SourceCurrentGateFrameResources.forecast firstPaths entry
      let secondary := SourceCurrentGateFrameResources.forecast firstPaths primary
      let signed := firstPaths.map (List.map Int.ofNat)
      let query := SourceCurrentConstrainedCapSeededForecast.finalProfile count signed secondary
      let guards := SourceCurrentSeededGuardForecast.finalAlphabet alphabet count signed secondary
      (guards, SourceCurrentConjunctionAlphabetBounds.callerForecast guards budget query)) ∧
    schedule budget count [firstPaths, lastPaths] alphabet entry = last ∧
    (Reserved bits budget count [firstPaths, lastPaths] alphabet entry ↔
      SourceCurrentConstrainedCapSeededForecast.SeededReserved bits count
        (firstPaths.map (List.map Int.ofNat))
        (SourceCurrentGateFrameResources.forecast firstPaths (SourceCurrentGateFrameResources.forecast firstPaths entry)) ∧
      SourceCurrentConstrainedCapSeededForecast.SeededReserved bits count
        (lastPaths.map (List.map Int.ofNat))
        (SourceCurrentGateFrameResources.forecast lastPaths (SourceCurrentGateFrameResources.forecast lastPaths first.2))) ∧
    fuel budget count [firstPaths, lastPaths] alphabet entry =
      max (classFuel budget count firstPaths alphabet entry)
        (classFuel budget count lastPaths first.1 first.2) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · constructor
    · intro reserved
      exact ⟨reserved.1, reserved.2.1⟩
    · intro reserved
      exact ⟨reserved.1, reserved.2, True.intro⟩
  · simp only [fuel, Nat.max_zero]

/-- Early exits and every component threshold below either class ceiling fit the same two-class fuel. -/
private theorem padded_stages (budget count : Nat) (firstPaths lastPaths : Class) (alphabet : List Guard) (entry : Profile) :
    let first := classStep budget count firstPaths alphabet entry
    let last := classStep budget count lastPaths first.1 first.2
    Le (SourceCurrentGateFrameResources.forecast firstPaths entry) last.2 ∧
    Le (SourceCurrentGateFrameResources.forecast firstPaths (SourceCurrentGateFrameResources.forecast firstPaths entry)) last.2 ∧
    alphabet ⊆ last.1 ∧
    (∀ phase, phase ≤ classFuel budget count firstPaths alphabet entry →
      phase ≤ fuel budget count [firstPaths, lastPaths] alphabet entry) ∧
    (∀ phase, phase ≤ classFuel budget count lastPaths first.1 first.2 →
      phase ≤ fuel budget count [firstPaths, lastPaths] alphabet entry) := by
  let first := classStep budget count firstPaths alphabet entry
  let last := classStep budget count lastPaths first.1 first.2
  have tailProfile : Le first.2 last.2 := classStep_profile_ge budget count lastPaths first.1 first.2
  have primaryFits := @Le.trans (SourceCurrentGateFrameResources.forecast firstPaths entry) first.2 last.2
    (classStep_primary_ge budget count firstPaths alphabet entry) tailProfile
  have secondaryFits := @Le.trans
    (SourceCurrentGateFrameResources.forecast firstPaths (SourceCurrentGateFrameResources.forecast firstPaths entry))
    first.2 last.2 (classStep_secondary_ge budget count firstPaths alphabet entry) tailProfile
  have guards := schedule_alphabet_ge budget count [firstPaths, lastPaths] alphabet entry
  have firstFuel : classFuel budget count firstPaths alphabet entry ≤
      fuel budget count [firstPaths, lastPaths] alphabet entry := by
    change _ ≤ max _ _
    exact Nat.le_max_left _ _
  have lastFuel : classFuel budget count lastPaths first.1 first.2 ≤
      fuel budget count [firstPaths, lastPaths] alphabet entry := by
    change _ ≤ max _ (max _ 0)
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  exact ⟨primaryFits, secondaryFits, guards,
    fun _ lower => Nat.le_trans lower firstFuel, fun _ lower => Nat.le_trans lower lastFuel⟩
/-- A concrete two-class schedule uses the length of a forest with an open placeholder. -/
def ordered_two_classes (bits budget : Nat) (alphabet : List Guard) (entry : Profile) :=
  ordered_stages bits budget placeholders.length firstPaths lastPaths alphabet entry

/-- Concrete early exits and phase thresholds retain that same original suffix schedule. -/
def padded_two_classes (budget : Nat) (alphabet : List Guard) (entry : Profile) :=
  padded_stages budget placeholders.length firstPaths lastPaths alphabet entry

end MicroCFTA.ScanForecastCheck
#check @MicroCFTA.ScanForecastCheck.ordered_two_classes
#print axioms MicroCFTA.ScanForecastCheck.ordered_two_classes
#check @MicroCFTA.ScanForecastCheck.padded_two_classes
#print axioms MicroCFTA.ScanForecastCheck.padded_two_classes

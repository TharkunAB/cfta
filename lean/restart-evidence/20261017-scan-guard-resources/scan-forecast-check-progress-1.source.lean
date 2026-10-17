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

#eval IO.eprintln "before ordered_two_classes"
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
  · change (_ ∧ _ ∧ True) ↔ (_ ∧ _)
    exact and_congr_right (fun _ => and_true _)
  · simp only [fuel, Nat.max_zero]

#eval IO.eprintln "after ordered_two_classes"
private noncomputable def phaseBounds (budget : Nat) (paths : Class) (alphabet : List Guard) (entry : Profile) : List Nat :=
  [SourceCurrentGateFrameResources.workerFuel paths entry,
    SourceCurrentGateFrameResources.workerFuel paths (SourceCurrentGateFrameResources.forecast paths entry),
    SourceCurrentConstrainedCapSeededForecast.fuel placeholders.length (paths.map (List.map Int.ofNat))
      (SourceCurrentGateFrameResources.forecast paths (SourceCurrentGateFrameResources.forecast paths entry)),
    SourceCurrentConjunctionWorklistResources.workerFuel (classStep budget placeholders.length paths alphabet entry).1 budget
      (SourceCurrentConstrainedCapTargetForecast.scalar
        (SourceCurrentConstrainedCapSeededForecast.finalProfile placeholders.length (paths.map (List.map Int.ofNat))
          (SourceCurrentGateFrameResources.forecast paths (SourceCurrentGateFrameResources.forecast paths entry)))),
    SourceCurrentConjunctionWorklistResources.readerFuel (classStep budget placeholders.length paths alphabet entry).1 budget
      (SourceCurrentConstrainedCapTargetForecast.scalar
        (SourceCurrentConstrainedCapSeededForecast.finalProfile placeholders.length (paths.map (List.map Int.ofNat))
          (SourceCurrentGateFrameResources.forecast paths (SourceCurrentGateFrameResources.forecast paths entry))))]
#eval IO.eprintln "before phase_le"
private theorem phase_le (budget : Nat) (paths : Class) (alphabet : List Guard) (entry : Profile)
    (phase : Nat) (member : phase ∈ phaseBounds budget paths alphabet entry) :
    phase ≤ classFuel budget placeholders.length paths alphabet entry := by
  have limits := classFuel_limits budget placeholders.length paths alphabet entry
  simp only [phaseBounds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact limits.1
  · exact limits.2.1
  · exact limits.2.2.1
  · exact limits.2.2.2.1
  · exact limits.2.2.2.2

#eval IO.eprintln "after phase_le"
/-- Early exits and both classes' five phase thresholds fit the same original suffix schedule. -/
theorem padded_two_classes (budget : Nat) (alphabet : List Guard) (entry : Profile) :
    let first := classStep budget placeholders.length firstPaths alphabet entry
    let last := classStep budget placeholders.length lastPaths first.1 first.2
    Le (SourceCurrentGateFrameResources.forecast firstPaths entry) last.2 ∧
    Le (SourceCurrentGateFrameResources.forecast firstPaths (SourceCurrentGateFrameResources.forecast firstPaths entry)) last.2 ∧
    alphabet ⊆ last.1 ∧
    (∀ phase ∈ phaseBounds budget firstPaths alphabet entry,
      phase ≤ fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry) ∧
    (∀ phase ∈ phaseBounds budget lastPaths first.1 first.2,
      phase ≤ fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry) := by
  let first := classStep budget placeholders.length firstPaths alphabet entry
  have tailProfile := classStep_profile_ge budget placeholders.length lastPaths first.1 first.2
  have primaryFits := (classStep_primary_ge budget placeholders.length firstPaths alphabet entry).trans tailProfile
  have secondaryFits := (classStep_secondary_ge budget placeholders.length firstPaths alphabet entry).trans tailProfile
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
    fun phase member => Nat.le_trans (phase_le budget firstPaths alphabet entry phase member) firstFuel,
    fun phase member => Nat.le_trans (phase_le budget lastPaths first.1 first.2 phase member) lastFuel⟩
#eval IO.eprintln "after padded_two_classes"
end MicroCFTA.ScanForecastCheck
#check @MicroCFTA.ScanForecastCheck.ordered_two_classes
#print axioms MicroCFTA.ScanForecastCheck.ordered_two_classes
#check @MicroCFTA.ScanForecastCheck.padded_two_classes
#print axioms MicroCFTA.ScanForecastCheck.padded_two_classes

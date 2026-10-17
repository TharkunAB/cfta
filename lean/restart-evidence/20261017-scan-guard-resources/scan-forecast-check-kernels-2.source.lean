import MicroCFTA.SourceCurrentScanNumericForecast
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
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
private def alphabet : List Guard := [⟨some [[[0], [1]]], .top⟩, SourceEqualityConstraintConstructors.top]
private noncomputable def primary (paths : Class) (profile : Profile) :=
  SourceCurrentGateFrameResources.forecast paths profile
private noncomputable def secondary (paths : Class) (profile : Profile) :=
  SourceCurrentGateFrameResources.forecast paths (primary paths profile)
private noncomputable def seeded (paths : Class) (profile : Profile) :=
  SourceCurrentConstrainedCapSeededForecast.finalProfile placeholders.length
    (paths.map (List.map Int.ofNat)) (secondary paths profile)
private noncomputable def seededAlphabet (paths : Class) (guards : List Guard) (profile : Profile) :=
  SourceCurrentSeededGuardForecast.finalAlphabet guards placeholders.length
    (paths.map (List.map Int.ofNat)) (secondary paths profile)
private noncomputable def memo (budget : Nat) (paths : Class) (guards : List Guard) (profile : Profile) :=
  SourceCurrentConjunctionAlphabetBounds.callerForecast (seededAlphabet paths guards profile) budget (seeded paths profile)
private noncomputable def firstAlphabet (entry : Profile) := seededAlphabet firstPaths alphabet entry
private noncomputable def firstProfile (budget : Nat) (entry : Profile) := memo budget firstPaths alphabet entry
private noncomputable def lastAlphabet (budget : Nat) (entry : Profile) := seededAlphabet lastPaths firstAlphabet entry (firstProfile budget entry)
private noncomputable def lastProfile (budget : Nat) (entry : Profile) := memo budget lastPaths firstAlphabet entry (firstProfile budget entry)

/-- Two original classes use primary, secondary, seeded, and memo predictions in that exact order. -/
theorem ordered_two_classes (bits budget : Nat) (entry : Profile) :
    placeholders = [.reference .depth, .empty] ∧
    schedule budget placeholders.length [firstPaths, lastPaths] alphabet entry =
      (lastAlphabet budget entry, lastProfile budget entry) ∧
    (Reserved bits budget placeholders.length [firstPaths, lastPaths] alphabet entry ↔
      SourceCurrentConstrainedCapSeededForecast.SeededReserved bits placeholders.length
        (firstPaths.map (List.map Int.ofNat)) (secondary firstPaths entry) ∧
      SourceCurrentConstrainedCapSeededForecast.SeededReserved bits placeholders.length
        (lastPaths.map (List.map Int.ofNat)) (secondary lastPaths (firstProfile budget entry))) ∧
    fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry =
      max (classFuel budget placeholders.length firstPaths alphabet entry)
        (classFuel budget placeholders.length lastPaths firstAlphabet entry (firstProfile budget entry)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change (_ ∧ _ ∧ True) ↔ (_ ∧ _)
    exact and_congr_right (fun _ => and_true _)
  · simp only [fuel, Nat.max_zero]
    rfl

private noncomputable def phaseBounds (budget : Nat) (paths : Class) (guards : List Guard) (profile : Profile) :=
  [SourceCurrentGateFrameResources.workerFuel paths profile,
    SourceCurrentGateFrameResources.workerFuel paths (primary paths profile),
    SourceCurrentConstrainedCapSeededForecast.fuel placeholders.length (paths.map (List.map Int.ofNat))
      (secondary paths profile),
    SourceCurrentConjunctionWorklistResources.workerFuel (seededAlphabet paths guards profile) budget
      (SourceCurrentConstrainedCapTargetForecast.scalar (seeded paths profile)),
    SourceCurrentConjunctionWorklistResources.readerFuel (seededAlphabet paths guards profile) budget
      (SourceCurrentConstrainedCapTargetForecast.scalar (seeded paths profile))]
private theorem phase_le (budget : Nat) (paths : Class) (guards : List Guard) (profile : Profile)
    (phase : Nat) (member : phase ∈ phaseBounds budget paths guards profile) :
    phase ≤ classFuel budget placeholders.length paths guards profile := by
  have limits := classFuel_limits budget placeholders.length paths guards profile
  simp only [phaseBounds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> omega

/-- Early class exits and all five phase thresholds fit the same ordered two-class schedule. -/
theorem padded_two_classes (budget : Nat) (entry : Profile) :
    Le (primary firstPaths entry) (lastProfile budget entry) ∧
    Le (secondary firstPaths entry) (lastProfile budget entry) ∧
    alphabet ⊆ lastAlphabet budget entry ∧
    (∀ phase ∈ phaseBounds budget firstPaths alphabet entry,
      phase ≤ fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry) ∧
    (∀ phase ∈ phaseBounds budget lastPaths firstAlphabet entry (firstProfile budget entry),
      phase ≤ fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry) := by
  have tailProfile := classStep_profile_ge budget placeholders.length lastPaths firstAlphabet entry (firstProfile budget entry)
  have primaryFits := (classStep_primary_ge budget placeholders.length firstPaths alphabet entry).trans tailProfile
  have secondaryFits := (classStep_secondary_ge budget placeholders.length firstPaths alphabet entry).trans tailProfile
  have guards := schedule_alphabet_ge budget placeholders.length [firstPaths, lastPaths] alphabet entry
  have firstFuel : classFuel budget placeholders.length firstPaths alphabet entry ≤
      fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry := by
    rw [(ordered_two_classes 0 budget entry).2.2.2]
    exact Nat.le_max_left _ _
  have lastFuel : classFuel budget placeholders.length lastPaths firstAlphabet entry (firstProfile budget entry) ≤
      fuel budget placeholders.length [firstPaths, lastPaths] alphabet entry := by
    rw [(ordered_two_classes 0 budget entry).2.2.2]
    exact Nat.le_max_right _ _
  exact ⟨primaryFits, secondaryFits, guards,
    fun phase member => Nat.le_trans (phase_le budget firstPaths alphabet entry phase member) firstFuel,
    fun phase member => Nat.le_trans (phase_le budget lastPaths firstAlphabet entry (firstProfile budget entry) phase member) lastFuel⟩

end MicroCFTA.ScanForecastCheck
#check @MicroCFTA.ScanForecastCheck.ordered_two_classes
#print axioms MicroCFTA.ScanForecastCheck.ordered_two_classes
#check @MicroCFTA.ScanForecastCheck.padded_two_classes
#print axioms MicroCFTA.ScanForecastCheck.padded_two_classes

import MicroCFTA.SourceCurrentParentGuardAlphabet
import MicroCFTA.SourceCurrentNativeClosedGuardAlphabet
import MicroCFTA.SourcePruningEnumerationForecastPathDomain

/-!
# Parent forecasts in one original closed guard alphabet

The input alphabet can be a subset of the fixed closed alphabet.
Every forecast stage stays in that closed alphabet.
The projected path carrier uses the original literals and initial state.
-/
namespace MicroCFTA.SourcePruningEnumerationClosedGuardForecast
open EqualityNormalize
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Profile" => SourceCurrentAllocatedNativeResourceForecast.Profile
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Core" => EnumerationState.State SourcePruningTemplates.Symbol Guard
local notation "Closed" => SourceCurrentNativeClosedGuardAlphabet.Closed
local notation "originalAlphabet" => SourceCurrentNativeClosedGuardAlphabet.originalAlphabet

private theorem advance_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (count : Nat) :
    SourceCurrentNativeGuardAlphabet.advance base count ⊆ alphabet := by
  induction count generalizing base with
  | zero => exact included
  | succ count ih =>
      exact ih ((SourceCurrentNativeGuardAlphabet.step_mono included).trans
        (SourceCurrentNativeClosedGuardAlphabet.step_subset alphabet closed))

private theorem query_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (profile : Profile) :
    SourceCurrentGeneratedQueryGuardResources.forecast base profile ⊆ alphabet :=
  advance_subset closed included _

private theorem seeded_fold_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (count : Nat) (seed : List Int)
    (paths : List (List Int)) (profile : Profile) :
    SourceCurrentSeededGuardForecast.foldAlphabet base count seed paths profile ⊆ alphabet := by
  induction paths generalizing profile with
  | nil => exact included
  | cons path rest ih => exact query_subset closed (ih _) _

private theorem seeded_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (count : Nat) (paths : List (List Int)) (profile : Profile) :
    SourceCurrentSeededGuardForecast.finalAlphabet base count paths profile ⊆ alphabet := by
  cases paths with
  | nil => exact included
  | cons seed rest => exact seeded_fold_subset closed included count seed rest profile

private theorem class_step_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (budget count : Nat) (paths : Class) (profile : Profile) :
    (SourceCurrentScanNumericForecast.classStep budget count paths base profile).1 ⊆ alphabet :=
  seeded_subset closed included count (paths.map (List.map Int.ofNat)) _

private theorem schedule_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (budget count : Nat) (classes : Constraints) (profile : Profile) :
    (SourceCurrentScanNumericForecast.schedule budget count classes base profile).1 ⊆ alphabet := by
  induction classes generalizing base profile with
  | nil => exact included
  | cons paths rest ih =>
      exact ih (base := (SourceCurrentScanNumericForecast.classStep budget count paths base profile).1)
        (profile := (SourceCurrentScanNumericForecast.classStep budget count paths base profile).2)
        (class_step_subset closed included budget count paths profile)

private theorem words_subset (base : List Guard) (limit : Nat) (word : List Guard)
    (member : word ∈ SourceCurrentParentAlphabetReservation.wordsThrough base limit) : word ⊆ base := by
  obtain ⟨count,_,selected⟩ := List.mem_flatMap.mp member
  exact ((SourceCurrentConjunctionTupleBounds.words_mem_iff base count word).mp selected).2

private theorem preparation_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (budget count : Nat)
    (records : List SourceEqualityClassOrder.Record) (profile : Profile) :
    SourceCurrentPreparationGuardAlphabet.forecast budget count records base profile ⊆ alphabet := by
  intro guard member
  obtain ⟨ambient,selected,returned⟩ := List.mem_flatMap.mp member
  exact schedule_subset closed ((words_subset base profile.edges ambient selected).trans included)
    budget count (records.map SourceEqualityClassOrder.Record.paths) profile returned

private theorem classes_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (budget count : Nat)
    (records : List SourceEqualityClassOrder.Record) (profile : Profile) :
    SourceCurrentClassesGuardAlphabet.forecast budget count records base profile ⊆ alphabet := by
  intro guard member
  rcases List.mem_append.mp member with earlier | later
  · rcases List.mem_append.mp earlier with original | prepared
    · exact included original
    · exact preparation_subset closed included budget count records profile prepared
  · obtain ⟨ambient,_,selected⟩ := List.mem_flatMap.mp later
    obtain ⟨kept,_,advanced⟩ := List.mem_flatMap.mp selected
    exact advance_subset closed (preparation_subset closed included budget count records profile) _ advanced

private theorem local_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    {width : Nat} (before : Checked width) (profile : Profile) :
    SourceCurrentLocalGuardAlphabet.forecast base budget count loaded inherited before profile ⊆ alphabet := by
  unfold SourceCurrentLocalGuardAlphabet.forecast
  split
  · exact classes_subset closed included _ _ _ _
  · exact included

/-- The complete Parent forecast stays in the same closed alphabet for every budget and profile. -/
theorem parent_forecast_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (budget count : Nat) (original : Guard)
    (loaded : Allocated) (inherited : EqValue) {width : Nat}
    (before : Checked width) (profile : Profile) (originalMember : original ∈ alphabet) :
    SourceCurrentParentGuardAlphabet.forecast base budget count original loaded inherited before profile ⊆ alphabet := by
  unfold SourceCurrentParentGuardAlphabet.forecast
  split
  · intro guard member
    rcases List.mem_cons.mp member with rfl | member
    · exact closed.1
    · exact included member
  · intro guard member
    rcases List.mem_cons.mp member with rfl | member
    · exact closed.1
    · rcases List.mem_cons.mp member with rfl | member
      · exact originalMember
      · exact local_subset closed included budget count loaded inherited before profile member

/-- A resident forecast needs only the original input-alphabet inclusion and original guard membership. -/
theorem resident_forecast_subset {alphabet base : List Guard} (closed : Closed alphabet)
    (included : base ⊆ alphabet) (budget : Nat) {width : Nat}
    (request : Request) (before : Checked width) (profile : Profile)
    (originalMember : request.value.entry.key.constraint ∈ alphabet) :
    SourceCurrentParentGuardAlphabet.residentForecast base budget request before profile ⊆ alphabet := by
  unfold SourceCurrentParentGuardAlphabet.residentForecast
  split
  · intro guard member
    rcases List.mem_cons.mp member with rfl | member
    · exact closed.1
    · exact included member
  · split
    · exact parent_forecast_subset closed included _ _ _ _ _ _ _ originalMember
    · exact included

/-- Every path in the full Parent forecast belongs to one finite original carrier. -/
theorem original_parent_projection_paths (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (initial : Core) (base : List Guard) (included : base ⊆ originalAlphabet literals)
    (budget count : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    {width : Nat} (before : Checked width) (profile : Profile)
    (originalMember : original ∈ originalAlphabet literals) :
    SourcePruningEnumerationPathTransport.ProjectionPaths
      (SourceCurrentParentGuardAlphabet.forecast base budget count original loaded inherited before profile)
      (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier (originalAlphabet literals) initial) := by
  intro guard member
  exact SourcePruningEnumerationForecastPathDomain.projected_paths (originalAlphabet literals) initial guard
    (parent_forecast_subset (SourceCurrentNativeClosedGuardAlphabet.original_closed literals normalized)
      included budget count original loaded inherited before profile originalMember member)

/-- Every path in the full resident forecast uses that same carrier for every budget and profile. -/
theorem original_resident_projection_paths (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (initial : Core) (base : List Guard) (included : base ⊆ originalAlphabet literals)
    (budget : Nat) {width : Nat} (request : Request) (before : Checked width) (profile : Profile)
    (originalMember : request.value.entry.key.constraint ∈ originalAlphabet literals) :
    SourcePruningEnumerationPathTransport.ProjectionPaths
      (SourceCurrentParentGuardAlphabet.residentForecast base budget request before profile)
      (fun path => path ∈ SourcePruningEnumerationForecastPathDomain.carrier (originalAlphabet literals) initial) := by
  intro guard member
  exact SourcePruningEnumerationForecastPathDomain.projected_paths (originalAlphabet literals) initial guard
    (resident_forecast_subset (SourceCurrentNativeClosedGuardAlphabet.original_closed literals normalized)
      included budget request before profile originalMember member)

end MicroCFTA.SourcePruningEnumerationClosedGuardForecast

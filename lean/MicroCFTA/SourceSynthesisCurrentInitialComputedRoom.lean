import MicroCFTA.SourceSynthesisCurrentCheckedHereditarySharedCompletion

/-!
# Mathematical initial word capacity from the current source input

The current source and its deterministic native build select one finite profile.
The exact initial worker forecast has the same profile at every cache and width.
The existing roomBits function supplies a sufficient mathematical width.
This does not prove capacity at a fixed Haskell machine width.
-/
namespace MicroCFTA.SourceSynthesisCurrentInitialComputedRoom
open Cache InternedConstructorTemplates
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialInitialization (emptyValue caller)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceCurrentSharedParentInitialRoom (roomBits room_computed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "envelope" => SourceCurrentSharedOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "cover" => SourceCurrentInitialSelectionForecast.cover

private noncomputable def initialProfile (budget : Nat) (value : Node)
    (heap : State Symbol Constraint) : Profile :=
  let output := envelope budget (count [] value) (mass value) (seed heap)
  cover [output.2.2.2]
    (SourceCurrentSharedOuterInitialSchedule.node output.1 budget (seed heap)).2

variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual current source and native build select the initial numeric profile. -/
noncomputable def profile (lib : Library) (query : Query) (signed : Int) (budget : Nat) : Profile :=
  match SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed with
  | .error _ => ⟨0, 0, 0, 0⟩
  | .ok expression =>
      match InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty with
      | .pending _ _ => ⟨0, 0, 0, 0⟩
      | .done value heap => initialProfile budget value heap

/-- The existing sufficient mathematical width uses only the original source input and budget. -/
noncomputable def bits (lib : Library) (query : Query) (signed : Int) (budget : Nat) : Nat :=
  roomBits (profile lib query signed budget)

/-- The same source and build identify the exact joined forecast at every initial cache and width. -/
theorem profile_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (budget : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
    (cache : Cache.State Key) (width : Nat) :
    let request : NodeRequest := ⟨emptyValue cache, value⟩
    let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
    profile lib query signed budget =
      cover [output.2.2.2]
        (forecast budget (SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request
          (caller width cache heap)) (seed heap)).2 := by
  obtain ⟨identity, same⟩ := SourceCurrentAllocatedPartialInitialization.emptyValue_live cache
  dsimp only
  calc
    profile lib query signed budget = initialProfile budget value heap := by
      simp only [profile, returned, built]
    _ = _ :=
      congrArg (fun inherited : SourceEqualityConstraintAllocation.Value =>
        let request : NodeRequest := ⟨inherited, value⟩
        let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
        cover [output.2.2.2]
          (forecast budget (SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request
            (caller width cache heap)) (seed heap)).2) same.symm

/-- The selected mathematical width satisfies the exact same-build checked-worker Room test. -/
theorem room_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (budget : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
    (cache : Cache.State Key) :
    let selected := bits lib query signed budget
    let request : NodeRequest := ⟨emptyValue cache, value⟩
    let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
    Room selected (cover [output.2.2.2]
      (forecast budget (SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request
        (caller (selected + 2) cache heap)) (seed heap)).2) := by
  dsimp only
  rw [← profile_of_build lib query signed expression returned budget value heap built cache
    (bits lib query signed budget + 2)]
  exact room_computed (profile lib query signed budget)

end MicroCFTA.SourceSynthesisCurrentInitialComputedRoom

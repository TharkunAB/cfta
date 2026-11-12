import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisOriginalSharedRankCompletion
import MicroCFTA.SourcePruningEnumerationSharedPreparedReservation

/-!
# Mathematical enumeration width from current source input

The original source and its deterministic native build select one profile.
The profile reserves the finite shared prepared enumeration at the requested depth.
The same source and build equations identify that exact reservation.
This result does not execute an initializer or worker.
It does not prove capacity at a fixed Haskell machine width.
-/
namespace MicroCFTA.SourceSynthesisCurrentProgramEnumerationWidth
open Cache InternedConstructorTemplates
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceSynthesisOriginalSharedRankCompletion (seed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The original source input selects the final finite-depth enumeration profile. -/
noncomputable def enumProfile (lib : Library) (query : Query) (signed : Int) (depth : Nat) : Profile :=
  match SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed with
  | .error _ => ⟨0, 0, 0, 0⟩
  | .ok expression =>
      match InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty with
      | .pending _ _ => ⟨0, 0, 0, 0⟩
      | .done _value heap =>
          (SourcePruningEnumerationSharedPreparedReservation.final depth (seed heap) 0).2

/-- The existing roomBits function selects a sufficient mathematical width. -/
noncomputable def enumBits (lib : Library) (query : Query) (signed : Int) (depth : Nat) : Nat :=
  SourceCurrentParentInitialRoom.roomBits (enumProfile lib query signed depth)

/-- The same actual current source and build identify the exact enumeration profile. -/
theorem enumProfile_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    enumProfile lib query signed depth =
      (SourcePruningEnumerationSharedPreparedReservation.final depth (seed heap) 0).2 := by
  simp only [enumProfile, returned, built]

/-- The chosen mathematical width reserves this same build at the requested depth. -/
theorem enum_reserved_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    SourcePruningEnumerationSharedPreparedReservation.Reserved
      (enumBits lib query signed depth) depth (seed heap) 0 := by
  unfold enumBits
  rw [enumProfile_of_build lib query signed expression returned depth value heap built]
  exact SourcePruningEnumerationSharedPreparedReservation.reserved_computed depth (seed heap) 0

end MicroCFTA.SourceSynthesisCurrentProgramEnumerationWidth

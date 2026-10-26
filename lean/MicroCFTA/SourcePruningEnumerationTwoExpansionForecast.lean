import MicroCFTA.SourcePruningEnumerationSiblingReservation

/-!
# One original envelope for two recursive expansions

The original profile pays the first narrowing prefix. Original suspended
mass bounds the inherited bucket and each retained prefix cache. One extra
paired stage covers a parked first expansion. The schedule supplies room
without asserting any future execution or endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationTwoExpansionForecast
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeResourceForecast (Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHook
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "headProfile" => SourceCurrentConstrainedCapEditForecast.headProfile
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "stage" => SourcePruningEnumerationSiblingReservation.stage
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationRecursiveReservation.afterHook
local notation "advance" => SourcePruningEnumerationIncomingReservation.advance

/-- The original narrowing prefix retains the alphabet and enlarges the numeric profile. -/
def start (seed : Seed) : Seed := (seed.1, headProfile seed.2)

/-- One extra paired stage covers the parked route even when the ordinary row bound is zero. -/
def rows (seed : Seed) : Nat := scalar (start seed).2 + 1

/-- The complete envelope depends only on the original seed and enumeration core. -/
noncomputable def final (seed : Seed) (before : Core) : Seed :=
  stage (start seed) (mass before) (mass before) (rows seed)

/-- Reserve all paired stages of the original envelope. -/
def Reserved (bits : Nat) (seed : Seed) (before : Core) : Prop :=
  SourcePruningEnumerationSiblingReservation.Reserved bits (start seed)
    (mass before) (mass before) (rows seed)

/-- The original envelope always contains its first paired stage. -/
theorem rows_positive (seed : Seed) : 1 ≤ rows seed := by
  unfold rows
  omega

/-- The first narrowing forecast retains the original numeric and alphabet bounds. -/
theorem start_ge (seed : Seed) : Le seed.2 (start seed).2 ∧ seed.1 ⊆ (start seed).1 := by
  change Le seed.2 (headProfile seed.2) ∧ seed.1 ⊆ seed.1
  constructor
  · exact SourceCurrentConstrainedCapEditForecast.headProfile_ge seed.2
  · exact fun _ member => member

/-- The complete original envelope bounds every shorter part of its same schedule. -/
theorem stage_le_final (seed : Seed) (before : Core) {count : Nat} (bounded : count ≤ rows seed) :
    Le (stage (start seed) (mass before) (mass before) count).2 (final seed before).2 ∧
      (stage (start seed) (mass before) (mass before) count).1 ⊆ (final seed before).1 :=
  SourcePruningEnumerationSiblingReservation.count_mono (start seed) (mass before) (mass before) bounded

/-- The original caller fits below the final envelope without changing its guard alphabet. -/
theorem final_ge (seed : Seed) (before : Core) :
    Le seed.2 (final seed before).2 ∧ seed.1 ⊆ (final seed before).1 := by
  have stages := SourcePruningEnumerationSiblingReservation.stage_ge
    (start seed) (mass before) (mass before) (rows seed)
  exact ⟨(start_ge seed).1.trans stages.1, fun _ member => stages.2 ((start_ge seed).2 member)⟩

/-- Current available rows and a nonincreasing selector fit the original ordinary row budget. -/
theorem selected_length_le {width : Nat} (seed : Seed) (caller : Caller width)
    (bounded : Fits (start seed).2 caller.checked)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (stored selected : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available caller.checked.native.machine.heap (.node entry stored depth free))
    (lengths : selected.length ≤ stored.length) : selected.length ≤ rows seed := by
  have heapFits : SourceCurrentConstrainedCapRequiredResources.HeapFits (start seed).2
      caller.checked.native.machine.heap :=
    SourceCurrentConstrainedCapRequiredResources.of_checked
      (profile := (start seed).2) (before := caller.checked) bounded
  have count := SourceCurrentConstrainedCapRequiredResources.node_width heapFits available
  exact Nat.le_trans lengths (Nat.le_trans count (Nat.le_succ _))

/-- The ordinary route uses a prefix of the original sibling reservation. -/
theorem Reserved.ordinary {bits : Nat} {seed : Seed} {before : Core}
    (reservation : Reserved bits seed before) (count : Nat) (bounded : count ≤ rows seed) :
    SourcePruningEnumerationSiblingReservation.Reserved bits (start seed)
      (mass before) (mass before) count :=
  SourcePruningEnumerationSiblingReservation.Reserved.prefix reservation bounded

/-- The original extra stage supplies both phases needed for the parked route. -/
theorem Reserved.first {bits : Nat} {seed : Seed} {before : Core}
    (reservation : Reserved bits seed before) :
    SourcePruningEnumerationRecursiveReservation.Reserved bits (start seed) (mass before) (mass before) :=
  SourcePruningEnumerationSiblingReservation.Reserved.head reservation

/-- A parked caller can use the planned head endpoint without executing an edge. -/
theorem parked_input_padding (seed : Seed) (before : Core) :
    Le seed.2 (afterHead (start seed) (mass before)).2 ∧
      seed.1 ⊆ (afterHead (start seed) (mass before)).1 := by
  have planned := SourcePruningEnumerationRecursiveReservation.afterHead_ge (start seed) (mass before)
  exact ⟨(start_ge seed).1.trans planned.1, fun _ member => planned.2 ((start_ge seed).2 member)⟩

/-- Clearing or retaining original buckets keeps the parked cache below the first mass ceiling. -/
theorem parked_mass_le (seed : Seed) (before checked : Core) (bounded : mass checked ≤ mass before) :
    mass checked ≤ SourcePruningEnumerationRecursiveReservation.massCeil
      (start seed) (mass before) (mass before) :=
  Nat.le_trans bounded (Nat.le_add_right _ _)

/-- The first paired reservation pays one actual resume from a mass-bounded parked cache. -/
theorem Reserved.parked {bits : Nat} {seed : Seed} {before : Core}
    (reservation : Reserved bits seed before) (checked : Core) (bounded : mass checked ≤ mass before) :
    SourcePruningEnumerationIncomingReservation.Reserved bits
      ((afterHead (start seed) (mass before)).1,
        headProfile (afterHead (start seed) (mass before)).2)
      (SourcePruningEnumerationExpansionAdmission.count (afterHead (start seed) (mass before)) checked) :=
  reservation.first.callback checked (parked_mass_le seed before checked bounded)

/-- The parked resume's actual shorter count fits the final original envelope. -/
theorem parked_final_padding (seed : Seed) (before checked : Core) (bounded : mass checked ≤ mass before) :
    Le (advance ((afterHead (start seed) (mass before)).1,
          headProfile (afterHead (start seed) (mass before)).2)
        (SourcePruningEnumerationExpansionAdmission.count (afterHead (start seed) (mass before)) checked)).2
        (final seed before).2 ∧
      (advance ((afterHead (start seed) (mass before)).1,
          headProfile (afterHead (start seed) (mass before)).2)
        (SourcePruningEnumerationExpansionAdmission.count (afterHead (start seed) (mass before)) checked)).1 ⊆
        (final seed before).1 := by
  have counts := SourcePruningEnumerationRecursiveReservation.callback_count_le
    (start seed) (mass before) (mass before) checked (parked_mass_le seed before checked bounded)
  have first := SourcePruningEnumerationRecursiveReservation.callback_padding
    (start seed) (mass before) (mass before)
    (SourcePruningEnumerationExpansionAdmission.count (afterHead (start seed) (mass before)) checked) counts
  have rest := stage_le_final seed before (count := 1) (rows_positive seed)
  exact ⟨first.1.trans rest.1, fun _ member => rest.2 (first.2 member)⟩

/-- Room at the original final forecast supplies every reserved stage. -/
theorem reserved_of_final_room (bits : Nat) (seed : Seed) (before : Core)
    (room : Room bits (final seed before).2) : Reserved bits seed before :=
  SourcePruningEnumerationSiblingReservation.reserved_of_final_room bits (start seed)
    (mass before) (mass before) (rows seed) room

/-- The original envelope computes a mathematical width for both execution routes. -/
theorem reserved_computed (seed : Seed) (before : Core) :
    Reserved (SourceCurrentParentInitialRoom.roomBits (final seed before).2) seed before :=
  reserved_of_final_room _ seed before (SourceCurrentParentInitialRoom.room_computed _)

end MicroCFTA.SourcePruningEnumerationTwoExpansionForecast

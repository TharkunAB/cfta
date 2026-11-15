import MicroCFTA.SourcePruningEnumerationSharedChildObservedResources
import MicroCFTA.SourcePruningEnumerationObservedPrefixFuel
import MicroCFTA.SourcePruningEnumerationPrefixIsolatedHistory
import MicroCFTA.SourcePruningEnumerationSharedChildIsolation
import MicroCFTA.SourceSynthesisProgramRolesSharedDriver
import MicroCFTA.SourceSynthesisProgramRolesUnmarkedWrite
import MicroCFTA.SourcePruningEnumerationIsolatedPending
import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourceSynthesisProgramRolesCompression
import MicroCFTA.SourceSynthesisProgramRolesClassAllocation
import MicroCFTA.SourceSynthesisProgramChildScope
import MicroCFTA.SourceSynthesisProgramParentCallbackRoles
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceSynthesisProgramRolesNativeHeap
import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
import MicroCFTA.SourcePruningEnumerationPrefixMass
import MicroCFTA.SourcePruningEnumerationSharedEagerCapturedBounds
import MicroCFTA.SourcePruningEnumerationSelectedPreparationCurrent
import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueResources
import MicroCFTA.SourcePruningEnumerationCostBounds
import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
import MicroCFTA.EnumerationStratifiedTransport
import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedPreparedZeroOutcomeResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningEnumerationSharedChildResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedOutcomeResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedReservation
import MicroCFTA.SourcePruningEnumerationIdentityPrefixCheckpoint

/-!
# Ordered mathematical reservations for eager children

The tuple forecast places its tail inside each child continuation.
Rows retain the captured mass ceiling and share the forecast seed.
The fallback phase also covers a terminal bucket at an ordinary node.
These definitions do not certify any execution or machine capacity.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)

/-- Pay one fallback bucket before its continuation forecast. -/
private noncomputable def fallbackPlan (bound ceiling : Nat)
    (continuation : Nat → Seed → Seed) (seed : Seed) : Seed :=
  continuation (ceiling + bound) (advance seed (bound + 1))

/-- Place the remaining tuple inside every child continuation forecast. -/
private noncomputable def tuplePlan
    (child : Nat → Nat → (Nat → Seed → Seed) → Seed → Seed) :
    Nat → Nat → Nat → (Nat → Seed → Seed) → Seed → Seed
  | 0, _bound, ceiling, continuation, seed => continuation ceiling seed
  | count + 1, bound, ceiling, continuation, seed =>
      child bound ceiling
        (fun reachedMass current => tuplePlan child count bound reachedMass continuation current) seed

/-- Reserve both bucket modes and every ordered ordinary row. -/
private noncomputable def nodePlan (limit own : Nat) :
    Nat → Nat → Nat → (Nat → Seed → Seed) → Seed → Seed
  | 0, bound, ceiling, continuation, seed => fallbackPlan bound ceiling continuation seed
  | height + 1, bound, ceiling, continuation, seed =>
      let first := fallbackPlan bound ceiling continuation seed
      iterate (fun current => tuplePlan (nodePlan limit own height)
        limit (bound + own) ceiling continuation current) first limit

/-- Derive the finite upper plan from the original depth, seed and mass ceiling. -/
noncomputable def eagerFinal : Nat → Seed → Nat → Seed
  | 0, seed, _ceiling => seed
  | depth + 1, seed, ceiling =>
      let captured := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
      let limit := SourceCurrentConstrainedCapTargetForecast.scalar captured.2
      let own := SourcePruningEnumerationGuardWidth.width captured.1
      nodePlan limit own limit ceiling ceiling
        (fun reachedMass current => eagerFinal depth current reachedMass) captured

private theorem fallbackPlan_ge (bound ceiling : Nat) (continuation : Nat → Seed → Seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1) (seed : Seed) :
    Le seed.2 (fallbackPlan bound ceiling continuation seed).2 ∧
      seed.1 ⊆ (fallbackPlan bound ceiling continuation seed).1 := by
  have first := SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed (bound + 1)
  have alphabet := SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge seed (bound + 1)
  have later := growth (ceiling + bound) (advance seed (bound + 1))
  exact ⟨first.trans later.1, fun _ member => later.2 (alphabet member)⟩

private theorem tuplePlan_ge
    (child : Nat → Nat → (Nat → Seed → Seed) → Seed → Seed)
    (childGrowth : ∀ bound ceiling continuation,
      (∀ retained current, Le current.2 (continuation retained current).2 ∧
        current.1 ⊆ (continuation retained current).1) →
      ∀ seed, Le seed.2 (child bound ceiling continuation seed).2 ∧
        seed.1 ⊆ (child bound ceiling continuation seed).1)
    (count : Nat) :
    ∀ bound ceiling continuation,
      (∀ retained current, Le current.2 (continuation retained current).2 ∧
        current.1 ⊆ (continuation retained current).1) →
      ∀ seed, Le seed.2 (tuplePlan child count bound ceiling continuation seed).2 ∧
        seed.1 ⊆ (tuplePlan child count bound ceiling continuation seed).1 := by
  induction count with
  | zero =>
      intro bound ceiling continuation growth seed
      exact growth ceiling seed
  | succ count ih =>
      intro bound ceiling continuation growth seed
      exact childGrowth bound ceiling
        (fun retained current => tuplePlan child count bound retained continuation current)
        (fun retained current => ih bound retained continuation growth current) seed

private theorem nodePlan_ge (limit own height : Nat) :
    ∀ bound ceiling continuation,
      (∀ retained current, Le current.2 (continuation retained current).2 ∧
        current.1 ⊆ (continuation retained current).1) →
      ∀ seed, Le seed.2 (nodePlan limit own height bound ceiling continuation seed).2 ∧
        seed.1 ⊆ (nodePlan limit own height bound ceiling continuation seed).1 := by
  induction height with
  | zero =>
      intro bound ceiling continuation growth seed
      exact fallbackPlan_ge bound ceiling continuation growth seed
  | succ height ih =>
      intro bound ceiling continuation growth seed
      let first := fallbackPlan bound ceiling continuation seed
      let row := fun current => tuplePlan (nodePlan limit own height)
        limit (bound + own) ceiling continuation current
      have initial := fallbackPlan_ge bound ceiling continuation growth seed
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) ih
          limit (bound + own) ceiling continuation growth current
      have later := iterate_ge row rowGrowth first limit
      exact ⟨initial.1.trans later.1, fun _ member => later.2 (initial.2 member)⟩

/-- The derived ordered forecast retains its original profile and guard alphabet. -/
theorem eagerFinal_ge (depth : Nat) (seed : Seed) (ceiling : Nat) :
    Le seed.2 (eagerFinal depth seed ceiling).2 ∧
      seed.1 ⊆ (eagerFinal depth seed ceiling).1 := by
  induction depth generalizing seed ceiling with
  | zero => exact ⟨Le.refl _, fun _ member => member⟩
  | succ depth ih =>
      let captured := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
      let limit := SourceCurrentConstrainedCapTargetForecast.scalar captured.2
      let own := SourcePruningEnumerationGuardWidth.width captured.1
      have initial := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
      have later := nodePlan_ge limit own limit ceiling ceiling
        (fun retained current => eagerFinal depth current retained)
        (fun retained current => ih current retained) captured
      exact ⟨initial.1.trans later.1, fun _ member => later.2 (initial.2 member)⟩

end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance advance_add)
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)
open SourcePruningEnumerationSharedPreparedReservation (preparedSeed)
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar

private theorem fallbackPlan_le_nodePlan (limit own height bound ceiling : Nat)
    (continuation : Nat → Seed → Seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1) (seed : Seed) :
    Le (fallbackPlan bound ceiling continuation seed).2
      (nodePlan limit own height bound ceiling continuation seed).2 ∧
    (fallbackPlan bound ceiling continuation seed).1 ⊆
      (nodePlan limit own height bound ceiling continuation seed).1 := by
  cases height with
  | zero => exact ⟨Le.refl _, fun _ member => member⟩
  | succ height =>
      exact iterate_ge (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current)
        (fun current => tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current)
        (fallbackPlan bound ceiling continuation seed) limit

private theorem first_callback_le_tuple
    (depth limit own height count bound ceiling : Nat) (seed : Seed) :
    let done := fun retained current => eagerFinal depth current retained
    let entry := advance seed (count * (bound + 1))
    let first := eagerFinal depth entry (ceiling + count * bound)
    let whole := tuplePlan (nodePlan limit own height) count bound ceiling done seed
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1 := by
  dsimp only
  induction count generalizing ceiling seed with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero, advance, tuplePlan]
      exact ⟨Le.refl _, fun _ member => member⟩
  | succ count ih =>
      let child := nodePlan limit own height
      let done := fun retained current => eagerFinal depth current retained
      let tail := fun retained current => tuplePlan child count bound retained done current
      have doneGrowth := fun retained current => eagerFinal_ge depth current retained
      have tailGrowth : ∀ retained current, Le current.2 (tail retained current).2 ∧
          current.1 ⊆ (tail retained current).1 := by
        intro retained current
        exact tuplePlan_ge child (nodePlan_ge limit own height)
          count bound retained done doneGrowth current
      have first := ih (ceiling + bound) (advance seed (bound + 1))
      have later := fallbackPlan_le_nodePlan limit own height bound ceiling tail tailGrowth seed
      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by
        rw [Nat.succ_mul]
        omega
      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by
        rw [Nat.succ_mul]
        omega
      rw [counts, advance_add, masses]
      exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩

private theorem first_row_callback_le_node (depth limit own height bound ceiling : Nat)
    (seed : Seed) (positive : 0 < limit) :
    let done := fun retained current => eagerFinal depth current retained
    let start := fallbackPlan bound ceiling done seed
    let first := eagerFinal depth (advance start (limit * (bound + own + 1)))
      (ceiling + limit * (bound + own))
    let whole := nodePlan limit own (height + 1) bound ceiling done seed
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1 := by
  dsimp only
  let done := fun retained current => eagerFinal depth current retained
  let start := fallbackPlan bound ceiling done seed
  let row := fun current => tuplePlan (nodePlan limit own height)
    limit (bound + own) ceiling done current
  have first := first_callback_le_tuple depth limit own height limit (bound + own) ceiling start
  have growth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
    intro current
    exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
      limit (bound + own) ceiling done (fun retained reached => eagerFinal_ge depth reached retained) current
  have later : Le (row start).2 (iterate row start limit).2 ∧
      (row start).1 ⊆ (iterate row start limit).1 := by
    obtain ⟨count, same⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    rw [same]
    exact iterate_ge row growth (row start) count
  exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩

/-- The first row contains its own padded callback after its planned child slots. -/
theorem first_row_callback_le_final (depth : Nat) (seed : Seed) (ceiling : Nat)
    (positive : 0 < scalar (preparedSeed seed).2) :
    let captured := preparedSeed seed
    let N := scalar captured.2
    let b := ceiling + SourcePruningEnumerationGuardWidth.width captured.1
    let rowStart := eagerFinal depth (advance captured (ceiling + 1)) (ceiling + ceiling)
    let first := eagerFinal depth (advance rowStart (N * (b + 1))) (ceiling + N * b)
    let whole := eagerFinal (depth + 1) seed ceiling
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1 := by
  let captured := preparedSeed seed
  let limit := scalar captured.2
  let own := SourcePruningEnumerationGuardWidth.width captured.1
  have currentPositive : 0 < limit := positive
  obtain ⟨height, same⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt currentPositive)
  have included := first_row_callback_le_node depth limit own height ceiling ceiling captured currentPositive
  have heightSame : height + 1 = limit := same.symm
  simpa only [heightSame, fallbackPlan, captured, limit, own, eagerFinal] using included

end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open SourceCurrentAllocatedNativeResourceForecast (Le Room)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge iterate_add)
open SourcePruningEnumerationSharedPreparedReservation (preparedSeed)
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar

private def fallbackReserved (bits bound ceiling : Nat)
    (admitted : Nat → Seed → Prop) (seed : Seed) : Prop :=
  SourcePruningEnumerationSharedIncomingReservation.Reserved bits seed (bound + 1) ∧
    admitted (ceiling + bound) (advance seed (bound + 1))

private def tupleReserved
    (child : Nat → Nat → (Nat → Seed → Seed) → Seed → Seed)
    (childReserved : Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop) :
    Nat → Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop
  | 0, _bound, ceiling, _continuation, admitted, seed => admitted ceiling seed
  | count + 1, bound, ceiling, continuation, admitted, seed =>
      childReserved bound ceiling
        (fun retained current => tuplePlan child count bound retained continuation current)
        (fun retained current => tupleReserved child childReserved count bound retained continuation admitted current)
        seed

private def nodeReserved (bits limit own : Nat) :
    Nat → Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop
  | 0, bound, ceiling, _continuation, admitted, seed => fallbackReserved bits bound ceiling admitted seed
  | height + 1, bound, ceiling, continuation, admitted, seed =>
      let first := fallbackPlan bound ceiling continuation seed
      let row := fun current => tuplePlan (nodePlan limit own height)
        limit (bound + own) ceiling continuation current
      fallbackReserved bits bound ceiling admitted seed ∧
        ∀ index, index < limit →
          tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
            limit (bound + own) ceiling continuation admitted (iterate row first index)

/-- Check native entry admission at every stage of the original ordered plan. -/
def eagerReserved (bits : Nat) : Nat → Seed → Nat → Prop
  | 0, _seed, _ceiling => True
  | depth + 1, seed, ceiling =>
      let captured := preparedSeed seed
      let limit := scalar captured.2
      let own := SourcePruningEnumerationGuardWidth.width captured.1
      nodeReserved bits limit own limit ceiling ceiling
        (fun retained current => eagerFinal depth current retained)
        (fun retained current => eagerReserved bits depth current retained) captured

private theorem iterate_index_le
    (next : Seed → Seed)
    (growth : ∀ current, Le current.2 (next current).2 ∧ current.1 ⊆ (next current).1)
    (seed : Seed) (first last : Nat) (counts : first ≤ last) :
    Le (iterate next seed first).2 (iterate next seed last).2 ∧
      (iterate next seed first).1 ⊆ (iterate next seed last).1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
  rw [iterate_add]
  exact iterate_ge next growth (iterate next seed first) extra

private theorem fallbackReserved_of_room (bits bound ceiling : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1)
    (accepted : ∀ retained current, Room bits (continuation retained current).2 → admitted retained current)
    (seed : Seed) (room : Room bits (fallbackPlan bound ceiling continuation seed).2) :
    fallbackReserved bits bound ceiling admitted seed := by
  have later := growth (ceiling + bound) (advance seed (bound + 1))
  exact ⟨SourcePruningEnumerationSharedIncomingReservation.reserved_of_final_room
      bits seed (bound + 1) (room.mono later.1),
    accepted (ceiling + bound) (advance seed (bound + 1)) room⟩

private theorem tupleReserved_of_room (bits : Nat)
    (child : Nat → Nat → (Nat → Seed → Seed) → Seed → Seed)
    (childReserved : Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop)
    (childGrowth : ∀ bound ceiling continuation,
      (∀ retained current, Le current.2 (continuation retained current).2 ∧
        current.1 ⊆ (continuation retained current).1) →
      ∀ seed, Le seed.2 (child bound ceiling continuation seed).2 ∧
        seed.1 ⊆ (child bound ceiling continuation seed).1)
    (childRoom : ∀ bound ceiling continuation admitted,
      (∀ retained current, Le current.2 (continuation retained current).2 ∧
        current.1 ⊆ (continuation retained current).1) →
      (∀ retained current, Room bits (continuation retained current).2 → admitted retained current) →
      ∀ seed, Room bits (child bound ceiling continuation seed).2 →
        childReserved bound ceiling continuation admitted seed)
    (count : Nat) :
    ∀ bound ceiling continuation admitted,
      (∀ retained current, Le current.2 (continuation retained current).2 ∧
        current.1 ⊆ (continuation retained current).1) →
      (∀ retained current, Room bits (continuation retained current).2 → admitted retained current) →
      ∀ seed, Room bits (tuplePlan child count bound ceiling continuation seed).2 →
        tupleReserved child childReserved count bound ceiling continuation admitted seed := by
  induction count with
  | zero =>
      intro bound ceiling continuation admitted growth accepted seed room
      exact accepted ceiling seed room
  | succ count ih =>
      intro bound ceiling continuation admitted growth accepted seed room
      exact childRoom bound ceiling
        (fun retained current => tuplePlan child count bound retained continuation current)
        (fun retained current => tupleReserved child childReserved count bound retained continuation admitted current)
        (fun retained current => tuplePlan_ge child childGrowth count bound retained continuation growth current)
        (fun retained current covered => ih bound retained continuation admitted growth accepted current covered)
        seed room

private theorem nodeReserved_of_room (bits limit own height : Nat) :
    ∀ bound ceiling continuation admitted,
      (∀ retained current, Le current.2 (continuation retained current).2 ∧
        current.1 ⊆ (continuation retained current).1) →
      (∀ retained current, Room bits (continuation retained current).2 → admitted retained current) →
      ∀ seed, Room bits (nodePlan limit own height bound ceiling continuation seed).2 →
        nodeReserved bits limit own height bound ceiling continuation admitted seed := by
  induction height with
  | zero =>
      intro bound ceiling continuation admitted growth accepted seed room
      exact fallbackReserved_of_room bits bound ceiling continuation admitted growth accepted seed room
  | succ height ih =>
      intro bound ceiling continuation admitted growth accepted seed room
      let first := fallbackPlan bound ceiling continuation seed
      let row := fun current => tuplePlan (nodePlan limit own height)
        limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      have firstBelow := iterate_ge row rowGrowth first limit
      constructor
      · exact fallbackReserved_of_room bits bound ceiling continuation admitted growth accepted seed
          (room.mono firstBelow.1)
      · intro index less
        have below := iterate_index_le row rowGrowth first (index + 1) limit (by omega)
        have nextEntry : iterate row first (index + 1) = row (iterate row first index) := by
          rw [iterate_add]
          rfl
        rw [nextEntry] at below
        have rowRoom : Room bits (row (iterate row first index)).2 := room.mono below.1
        exact tupleReserved_of_room bits (nodePlan limit own height) (nodeReserved bits limit own height)
          (nodePlan_ge limit own height) ih limit (bound + own) ceiling continuation admitted growth accepted
          (iterate row first index) rowRoom

/-- Room at the computed original plan supplies every planned query entry. -/
theorem eagerReserved_of_final_room (bits depth : Nat) (seed : Seed) (ceiling : Nat)
    (room : Room bits (eagerFinal depth seed ceiling).2) :
    eagerReserved bits depth seed ceiling := by
  induction depth generalizing seed ceiling with
  | zero => trivial
  | succ depth ih =>
      simp only [eagerReserved]
      simp only [eagerFinal] at room
      generalize preparedSeed seed = captured at room ⊢
      generalize scalar captured.2 = limit at room ⊢
      generalize SourcePruningEnumerationGuardWidth.width captured.1 = own at room ⊢
      exact nodeReserved_of_room bits limit own limit ceiling ceiling
        (fun retained current => eagerFinal depth current retained)
        (fun retained current => eagerReserved bits depth current retained)
        (fun retained current => eagerFinal_ge depth current retained)
        (fun retained current covered => ih current retained covered) captured room

end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (OutcomeResources Output Failure finish)
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
variable {Typing : Type} {bits : Nat}
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Visitor" => List Suspended → Node → Caller (bits + 2) → Cached → Queries →
  (Fragment → Caller (bits + 2) → Queries → Cached → Fold) →
  (ChildDispatch.Observation (bits + 2) → Option Cached → Fold) → Fold

-- Private fragment for the existing SharedEagerReservation namespace and aliases.
-- Insert before ActualFallback, outside its Symbol/Node instance section.
section EagerOutputReturnFoundation
variable [DecidableEq (EdgeKey Symbol Constraint)]

-- Proposed PRIVATE contracts in SharedEagerReservation with only EdgeKey DecidableEq in scope.
private def OutcomeResourcesWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (seed : Seed)
    (outcome : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) : Prop :=
  OutcomeResources formulas solver original seed outcome ∧
    ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted outcome, outputOK output

-- The concrete Program-role instantiation. This has no native execution input.
omit [DecidableEq (EdgeKey Symbol Constraint)] in
private def programOutputRoles
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (output : Output (bits + 2) Typing) : Prop :=
  ∃ extended : Nat → Prop,
    (∀ uv, marked uv → extended uv) ∧
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
      SourceSynthesisLabelProgramBuildRoles.literal
      output.caller.checked.native.machine.heap output.cache.core extended

omit [DecidableEq (EdgeKey Symbol Constraint)] in
/-- Concrete outputs retain Program roles and original isolated boundaries. -/
private def programOutputRolesWithIsolated
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (caller : Caller (bits + 2)) (before : Cached)
    (output : Output (bits + 2) Typing) : Prop :=
  programOutputRoles valid marked output ∧
    ∀ held handle (value : Node),
      EnumerationDischargeHistory.IsolatedPending held handle before.core →
      SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some value →
      MergedOrdinaryHeight.recursiveBoundary value = true →
      EnumerationDischargeHistory.IsolatedPending held handle output.cache.core ∧
        SourcePruningEnumerationNodes.lookupNode output.caller.checked.native.machine.heap handle = some value

-- The local observer excludes only the raw slot written by its head.
omit [DecidableEq (EdgeKey Symbol Constraint)] in
private def programOutputRolesWithIsolatedExcept
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (caller : Caller (bits + 2)) (before : Cached) (target : Nat)
    (output : Output (bits + 2) Typing) : Prop :=
  programOutputRoles valid marked output ∧
    ∀ held handle (value : Node),
      held ≠ target →
      EnumerationDischargeHistory.IsolatedPending held handle before.core →
      SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some value →
      MergedOrdinaryHeight.recursiveBoundary value = true →
      EnumerationDischargeHistory.IsolatedPending held handle output.cache.core ∧
        SourcePruningEnumerationNodes.lookupNode output.caller.checked.native.machine.heap handle = some value

local notation "Receipt" => SelectedEdge.Result (bits + 2)
local notation "Stopped" => NativeContinuations.Stop (Failure (bits + 2) Typing) (bits + 2)
variable {outputOK : Output (bits + 2) Typing → Prop}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {original middle : Caller (bits + 2)} {middleInventory : Inventory} {middleMemos : Memos}
variable {seed larger : Seed}

private theorem resources_outputs_mono
    {outcome : NativeContinuations.HookResult
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)}
    (numeric : SourceCurrentAllocatedNativeResourceForecast.Le seed.2 larger.2)
    (alphabet : seed.1 ⊆ larger.1)
    (resources : OutcomeResourcesWithOutputs outputOK formulas solver original seed outcome) :
    OutcomeResourcesWithOutputs outputOK formulas solver original larger outcome := by
  exact ⟨resources.1.mono numeric alphabet, resources.2⟩

private theorem resources_outputs_post
    {outcome : NativeContinuations.HookResult
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)}
    (post : Post formulas solver middleInventory original middle middleMemos)
    (resources : OutcomeResourcesWithOutputs outputOK formulas solver middle seed outcome) :
    OutcomeResourcesWithOutputs outputOK formulas solver original seed outcome := by
  exact ⟨resources.1.post post, resources.2⟩

private theorem resources_outputs_true_iff
    {outcome : NativeContinuations.HookResult
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)} :
    OutcomeResourcesWithOutputs (fun (_ : Output (bits + 2) Typing) => True) formulas solver original seed outcome ↔
      OutcomeResources formulas solver original seed outcome := by
  constructor
  · intro resources
    exact resources.1
  · intro resources
    exact ⟨resources, fun _ _ => True.intro⟩

private theorem resources_outputs_finish
    (uv : Nat) (folded : Fold)
    (resources : OutcomeResources formulas solver original seed (finish uv folded))
    (held : ∀ output ∈ (match folded with
      | .complete _ outputs _ _ => outputs
      | .stopped _ outputs _ => outputs), outputOK output) :
    OutcomeResourcesWithOutputs outputOK formulas solver original seed (finish uv folded) := by
  cases folded <;> exact ⟨resources, held⟩

private theorem resources_outputs_append
    (uv : Nat) (processed : List Receipt) (headOutputs : List (Output (bits + 2) Typing))
    (later : Fold)
    (post : Post formulas solver middleInventory original middle middleMemos)
    (numeric : SourceCurrentAllocatedNativeResourceForecast.Le seed.2 larger.2)
    (alphabet : seed.1 ⊆ larger.1)
    (head : OutcomeResourcesWithOutputs outputOK formulas solver original seed
      (.complete headOutputs middle middleMemos.query))
    (tail : OutcomeResourcesWithOutputs outputOK formulas solver middle larger (finish uv later)) :
    let combined := match (generalizing := false) later with
      | .complete receipts outputs reached queries =>
          .complete (processed ++ receipts) (headOutputs ++ outputs) reached queries
      | .stopped receipts outputs current =>
          .stopped (processed ++ receipts) (headOutputs ++ outputs) current
    OutcomeResourcesWithOutputs outputOK formulas solver original larger (finish uv combined) := by
  have headWide := resources_outputs_mono numeric alphabet head
  have tailAt := resources_outputs_post post tail
  obtain ⟨_headCaller, _headInventory, _headMemos, _headPost, _headFits, _headKnown,
    _headCallerSame, _headQuerySame, headValid⟩ := headWide.1
  cases later with
  | complete receipts outputs reached queries =>
      obtain ⟨actual, next, final, returnedPost, fitted, known, callerSame, querySame, tailValid⟩ := tailAt.1
      constructor
      · refine ⟨actual, next, final, returnedPost, fitted, known, callerSame, querySame, ?_⟩
        intro output member
        rcases List.mem_append.mp member with old | fresh
        · exact headValid output old
        · exact tailValid output fresh
      · intro output member
        rcases List.mem_append.mp member with old | fresh
        · exact headWide.2 output old
        · exact tailAt.2 output fresh
  | stopped receipts outputs current =>
      obtain ⟨actual, next, final, returnedPost, fitted, known, observed, tailValid⟩ := tailAt.1
      constructor
      · refine ⟨actual, next, final, returnedPost, fitted, known, observed, ?_⟩
        intro output member
        rcases List.mem_append.mp member with old | fresh
        · exact headValid output old
        · exact tailValid output fresh
      · intro output member
        rcases List.mem_append.mp member with old | fresh
        · exact headWide.2 output old
        · exact tailAt.2 output fresh

private theorem resources_outputs_scan_stopped
    (uv : Nat)
    (visit : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold)
    (before : Cached) (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller : Caller (bits + 2)) (queries : Queries)
    (processed : List Receipt) (outputs : List (Output (bits + 2) Typing)) (current : Stopped)
    (observed : visit edge caller queries before = .stopped processed outputs current)
    (resources : OutcomeResourcesWithOutputs outputOK formulas solver original seed
      (finish uv (.stopped processed outputs current))) :
    OutcomeResourcesWithOutputs outputOK formulas solver original seed
      (finish uv (SourcePruningEnumerationSharedBranching.scan visit before (edge :: rest) caller queries)) := by
  rw [SourcePruningEnumerationSharedBranching.scan_stopped visit before edge rest caller queries
    processed outputs current observed]
  exact resources

end EagerOutputReturnFoundation

section ActualFallback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem fallback_complete_resources_cps
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (bucket : List Suspended) (incoming : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 caller.checked)
    (reserved : SourcePruningEnumerationSharedIncomingReservation.Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) bucket incoming caller before memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed bucket →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
        PendingFragment after.core fragment ∧
        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
          Avoids before.core.representatives held bucket →
          FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap) ∧
      (∀ er en P H ek, p ≤ P → h ≤ H →
        ∀ (done : Fragment → Caller (bits + 2) → Queries → Cached → Fold)
          (stopped : ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
        SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (r + er) (n + en) P H (k + ek)
          edgesOf bucket incoming caller before memos.query done stopped =
          match raw with
          | [.ok (fragment, _returned)] => done fragment afterCaller savedQueries after
          | _ => stopped ((.ok (some raw), afterCaller, savedQueries, outer, waiting)) (some after)) := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, retained⟩ :=
    ChildDispatch.complete_with_fragments_resources seed formulas solver inventory caller before checkEmpty bucket
      incoming roots memos packet.context packet.safe paths counts flags realized bounded pending available closed
      fits reserved known
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, retained, ?_⟩
  intro er en P H ek representative native done stopped
  rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty (r + er) (n + en) P H (k + ek)
    edgesOf bucket incoming caller before memos.query done stopped fallback]
  unfold SourcePruningEnumerationSharedChildVisitors.shallowVisit
  rw [retained.1 er en P H ek representative native]
  cases raw with
  | nil => rfl
  | cons first rest =>
      cases first with
      | error fault => rfl
      | ok returned =>
          rcases returned with ⟨fragment, core⟩
          cases rest <;> rfl
end ActualFallback

section ActualTuple
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem visitChildren_nil_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (seed : Seed) (uv : Nat) (visit : Visitor)
    (done : List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (actual : OutcomeResources formulas solver original seed (finish uv (done [] caller queries before))) :
    OutcomeResources formulas solver original seed (finish uv
      (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped [] caller before queries)) := actual

private theorem visitChildren_cons_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (seed : Seed) (uv : Nat) (visit : Visitor)
    (done : List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (good : Fragment → Caller (bits + 2) → Queries → Cached → Prop)
    (bad : ChildDispatch.Observation (bits + 2) → Option Cached → Prop)
    (head : ∀ yes no,
      (∀ fragment reached saved after, good fragment reached saved after →
        OutcomeResources formulas solver original seed (finish uv (yes fragment reached saved after))) →
      (∀ observation candidate, bad observation candidate →
        OutcomeResources formulas solver original seed (finish uv (no observation candidate))) →
      OutcomeResources formulas solver original seed (finish uv
        (visit bucket incoming caller before queries yes no)))
    (tail : ∀ fragment reached saved after, good fragment reached saved after →
      OutcomeResources formulas solver original seed (finish uv
        (SourcePruningEnumerationSharedChildVisitors.visitChildren visit
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved)))
    (failed : ∀ observation candidate, bad observation candidate →
      OutcomeResources formulas solver original seed (finish uv (stopped [] observation candidate))) :
    OutcomeResources formulas solver original seed (finish uv
      (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped
        ((incoming, bucket) :: rest) caller before queries)) := by
  exact head
    (fun fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren visit
      (fun fragments => done (fragment :: fragments))
      (fun completed => stopped (fragment :: completed)) rest reached after saved)
    (fun observation candidate => stopped [] observation candidate) tail failed
end ActualTuple


section ActualZero
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem resume_eager_zero_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (decision : Option Next) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ outcome,
      (∀ workFuel, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
        metadata caller memos.query before decision = outcome) ∧
      OutcomeResources formulas solver caller seed outcome := by
  obtain ⟨outcome, running, resources⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.resume_zero_outcome_resources holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata decision seed packet bounded known
  refine ⟨outcome, ?_, resources⟩
  intro workFuel
  rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resume_zero]
  cases decision with
  | none => simpa only [SourcePruningEnumerationSharedPreparedRecursive.resume] using running workFuel
  | some selected =>
      cases selected <;> simpa only [SourcePruningEnumerationSharedPreparedRecursive.resume] using running workFuel
end ActualZero

section ActualOrdinaryPrefix
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem ordinary_prefix_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    ∃ (roots : Nat → Nat) (action : EnumerateM Symbol Constraint
        (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint))
      (own : Cached),
      Roots before.core.representatives roots ∧
      (SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol,
          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own)] ∧
      ExceptT.run (action before.core) =
        [.ok ((edge.entry.key.symbol,
          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own.core)] ∧
      own.core = suspendedState tries.length before.core ∧
      own.core.counter = before.core.counter + tries.length ∧
      own.core.representatives = before.core.representatives ∧
      Safe own.core ∧ Roots own.core.representatives roots ∧ PendingRealized caller.checked.native.machine.heap own.core ∧
      EnumerationCanonicalWaiting.Correct roots own.core.values own.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((own.core.values[slot]?).getD .eliminated) = some (own.expandable slot)) ∧
      InputsPending own.core (scs ++ suspendedVars before.core.counter tries) ∧
      (∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
        Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
        (∀ sc ∈ bucket, sc.var < own.core.counter) ∧ InputsPending own.core bucket) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs →
        EnumerationDriver.Protected held before.core own.core ∧
          ∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
            Avoids own.core.representatives held bucket)) ∧
      Packet formulas solver inventory caller memos metadata own ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound own.core =
        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
      (∀ child bucket, (child, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
        MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry edges depth free)) ∧
      ∀ (visit : Visitor) (consume : SelectedEdge.Result (bits + 2) → Fold),
        SourcePruningEnumerationSharedChildVisitors.visitSelected visit consume scs edge caller before memos.query =
          SourcePruningEnumerationSharedChildVisitors.visitChildren visit
            (fun fragments reached saved after =>
              let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
              consume (.complete fragment reached saved (SelectedEdge.finish residual fragment after)))
            (fun completed observation candidate => consume (.stopped completed observation candidate))
            (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) caller own memos.query := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨action, own, retained⟩ := SourcePruningEnumerationEdgeInputs.complete
    caller.checked.native.machine.heap parentEntry edges depth free edge scs roots
    packet.context.ready.semantic.ready parentAvailable parentClosed selected before packet.safe realized
    paths counts flags bounded pending allowed tries residual projected
  refine ⟨roots, action, own, paths, retained, ?_⟩
  obtain ⟨_prepared, ownRun, _raw, ownCore, ownCounter, _ownForest, ownSafe,
    ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, _genuine, _ownProtects⟩ := retained
  have origin : EnumeratedOrigin before.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length before.core
  have protects (held : Nat) (inside : held < before.core.counter)
      (root : IsRoot before.core.representatives held) :
      EnumerationDriver.Protected held before.core own.core := by
    rw [ownCore]
    exact EnumerationDriver.suspension_protected held tries.length before.core packet.safe inside root
  have protectsEnumerated (held : Nat) (fragment : Fragment)
      (stored : before.core.values[held]? = some (.enumerated fragment)) :
      EnumerationDriver.Protected held before.core own.core := by
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held fragment stored
    exact protects held inside root
  have afterPending : EnumerationReferences.PendingReferences own.core := by
    intro held fragment stored
    have previous := origin held fragment stored
    have incoming : EnumerationReferences.ReferencesAllowed
        (fun uv => ¬UnionFind.SameClass before.core.representatives held uv) own.core := by
      rw [ownCore]
      exact EnumerationReferences.suspension_allowed _ tries.length before.core
        (packet.pending held fragment previous)
    intro value member sc listed related
    exact incoming value member sc listed (((protectsEnumerated held fragment previous).classes sc.var).mp related)
  have growth : before.core.counter ≤ own.core.counter := by rw [ownCounter]; omega
  have ownPacket : Packet formulas solver inventory caller memos metadata own := by
    refine ⟨packet.context, ownSafe, afterPending,
      ⟨roots, ownPaths, ownSafe.1, ownRealized, ownCounts, ownFlags⟩, ?_, ?_⟩
    · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
      obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core own.core
        ownSafe level frontier oldOrder origin protectsEnumerated
      exact ⟨nextLevel, frontier, afterOrder⟩
    · intro group member entry listed
      exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  let staged := inputs.map (fun input =>
    (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
  have actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), own)] := ownRun
  have readback : staged.map (fun input => (input.1, input.2.1)) = inputs := by
    dsimp only [staged]
    simp only [List.map_map]
    exact List.map_id _
  refine ⟨ownPacket, ?_, ?_, ?_⟩
  · rw [ownCore]
    exact (SourcePruningEnumerationCachedOwn.suspendedState_scalars tries.length before.core).2
  · intro child bucket member
    obtain ⟨_tries, _projected, _inputs, lower⟩ := SourcePruningEnumerationSharedEagerChildren.prepared_child_lt
      caller.checked.native.machine.heap parentEntry edges depth free edge selected scs before own
      edge.entry.key.symbol staged residual actual child bucket (by rw [readback]; exact member)
    exact lower
  · intro visit consume
    unfold SourcePruningEnumerationSharedChildVisitors.visitSelected
    rw [actual]
    simp only []
    rw [readback]
end ActualOrdinaryPrefix

section ActualEagerCallback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Index completion by the narrowing operation used by the actual recursive worker. -/
private def EagerResumeWithNarrowComplete
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    eagerReserved bits recursiveDepth seed ceiling →
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (bound + extra) (bound + extra)
          (bound + extra) (bound + extra) (bound + extra) edgesOf)
        narrow graph templates checkEmpty edgesOf stop order (bound + extra) recursiveDepth
        metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome

/-- The actual Left callback uses completion at the smaller recursive depth. -/
private theorem callback_eager_induction_resources_with_narrow
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerResumeWithNarrowComplete (bits := bits) narrow graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          narrow graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    narrow graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith (recur (fuel + extra))
      graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
    OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
  obtain ⟨callbackFuel, result, after, returned, _stable, frame, _types, _holes, _typing,
    _currentFits, _currentKnown, callback⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver inventory graph templates
      metadata uv fragment caller memos before seed packet allocated bounded known
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth seed ceiling
    refine ⟨callbackFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2⟩
    intro extra
    rw [(callback extra).2.2 (recur (callbackFuel + extra)) stop order, ite_eq_left rejected]
  · have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
        (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change SourcePruningEnumerationPrefixAdmission.suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved
    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources⟩
    intro extra
    have actual := callback (resumeFuel + extra)
    rw [← Nat.add_assoc] at actual
    rw [actual.2.2 (recur (callbackFuel + resumeFuel + extra)) stop order, ite_eq_right rejected]
    have observed := running (callbackFuel + extra)
    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
    rw [common] at observed
    exact observed
variable {Key : Type}

private def EagerResumeComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) : Prop :=
  EagerResumeWithNarrowComplete (bits := bits) (SourcePruningOuterNarrow.narrow holeKey fits admits)
    graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth

private theorem eager_resume_zero_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength _mass _reserved
  obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey fits admits graph templates
    checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata
    (SourcePruningEnumerationRestart.decision stop order metadata before) seed packet bounded known
  exact ⟨0, outcome, fun extra => running (0 + extra), resources⟩

private theorem callback_eager_induction_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
  exact callback_eager_induction_resources_with_narrow
    (SourcePruningOuterNarrow.narrow holeKey fits admits)
    formulas solver inventory graph templates metadata uv fragment caller memos before checkEmpty edgesOf
    stop order recursiveDepth recursive seed ceiling packet allocated bounded known
    selectionMembers selectionLength mass reserved

end ActualEagerCallback

open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (advance_add)

private theorem nodeReserved_fallback (bits limit own height bound ceiling : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
    (reserved : nodeReserved bits limit own height bound ceiling continuation admitted seed) :
    fallbackReserved bits bound ceiling admitted seed := by
  cases height with
  | zero => exact reserved
  | succ height => exact reserved.1

private theorem tupleReserved_first_callback (bits limit own height count bound ceiling : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed) :
    admitted (ceiling + count * bound) (advance seed (count * (bound + 1))) := by
  induction count generalizing ceiling seed with
  | zero => simpa only [tupleReserved, Nat.zero_mul, Nat.add_zero, advance] using reserved
  | succ count ih =>
      let tail := fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current
      let covered := fun retained current => tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
        count bound retained continuation admitted current
      have child : nodeReserved bits limit own height bound ceiling tail covered seed := reserved
      have later := ih (ceiling + bound) (advance seed (bound + 1))
        (nodeReserved_fallback bits limit own height bound ceiling tail covered seed child).2
      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by rw [Nat.succ_mul]; omega
      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by rw [Nat.succ_mul]; omega
      rw [counts, advance_add, masses]
      exact later

private theorem first_callback_le_tuple_of_growth (limit own height count bound ceiling : Nat)
    (continuation : Nat → Seed → Seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1) (seed : Seed) :
    Le (continuation (ceiling + count * bound) (advance seed (count * (bound + 1)))).2
      (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed).2 ∧
    (continuation (ceiling + count * bound) (advance seed (count * (bound + 1)))).1 ⊆
      (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed).1 := by
  induction count generalizing ceiling seed with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero, advance, tuplePlan]
      exact ⟨Le.refl _, fun _ member => member⟩
  | succ count ih =>
      let child := nodePlan limit own height
      let tail := fun retained current => tuplePlan child count bound retained continuation current
      have tailGrowth : ∀ retained current, Le current.2 (tail retained current).2 ∧
          current.1 ⊆ (tail retained current).1 := by
        intro retained current
        exact tuplePlan_ge child (nodePlan_ge limit own height) count bound retained continuation growth current
      have first := ih (ceiling + bound) (advance seed (bound + 1))
      have later := fallbackPlan_le_nodePlan limit own height bound ceiling tail tailGrowth seed
      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by rw [Nat.succ_mul]; omega
      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by rw [Nat.succ_mul]; omega
      rw [counts, advance_add, masses]
      exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩

section ActualTuplePadding
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem tuple_nil_reserved_resources_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed)
    (admitted : Nat → Seed → Prop)
    (growth : ∀ retained current, SourceCurrentAllocatedNativeResourceForecast.Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (caller : Caller (bits + 2))
    (memos : Memos) (before : Cached) (uv : Nat)
    (visit : Nat → Visitor)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed)
    (consumer : ∀ retained current,
      Fits current.2 caller.checked →
      Heap (fun guard => guard ∈ current.1) caller.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) [] caller memos.query before = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver caller (continuation retained current) (finish uv outcome)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren (visit (fuel + extra))
        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
  let entry := advance seed (count * (bound + 1))
  have entryFits : Fits entry.2 caller.checked := fits.mono
    (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed (count * (bound + 1)))
  have entryKnown : Heap (fun guard => guard ∈ entry.1) caller.checked.native.machine.heap := by
    intro key edge found
    exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge seed
      (count * (bound + 1)) (known key edge found)
  have entryMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling + count * bound :=
    Nat.le_trans mass (Nat.le_add_right _ _)
  have entryAdmitted : admitted (ceiling + count * bound) entry :=
    tupleReserved_first_callback bits limit own height count bound ceiling continuation admitted seed reserved
  obtain ⟨fuel, outcome, running, resources⟩ := consumer (ceiling + count * bound) entry
    entryFits entryKnown entryMass entryAdmitted
  have included := first_callback_le_tuple_of_growth limit own height count bound ceiling continuation growth seed
  exact ⟨fuel, outcome, running, resources_outputs_mono included.1 included.2 resources⟩

private theorem tuple_nil_reserved_resources
    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed)
    (admitted : Nat → Seed → Prop)
    (growth : ∀ retained current, SourceCurrentAllocatedNativeResourceForecast.Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (caller : Caller (bits + 2))
    (memos : Memos) (before : Cached) (uv : Nat)
    (visit : Nat → Visitor)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed)
    (consumer : ∀ retained current,
      Fits current.2 caller.checked →
      Heap (fun guard => guard ∈ current.1) caller.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) [] caller memos.query before = outcome) ∧
        OutcomeResources formulas solver caller (continuation retained current) (finish uv outcome)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren (visit (fuel + extra))
        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
  simpa only [resources_outputs_true_iff] using
    (tuple_nil_reserved_resources_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) limit own height count bound ceiling continuation admitted growth seed formulas solver caller memos before uv visit done stopped fits known mass reserved
      (by simpa only [resources_outputs_true_iff] using consumer))
end ActualTuplePadding

section ActualChildInputs
variable [DecidableEq (EdgeKey Symbol Constraint)]

private def ChildInputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended)
    (fragment : Fragment) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached) : Prop :=
  ∃ (next : Inventory) (final : Memos),
    Post formulas solver next original reached final ∧ final.query = queries ∧
    Packet formulas solver next reached final metadata after ∧ before.core.counter ≤ after.core.counter ∧
    EnumeratedOrigin before.core after.core ∧
    (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
    (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
      EnumerationReferences.InputsAllowed allowed bucket →
      (∀ uv, before.core.counter ≤ uv → allowed uv) →
      EnumerationReferences.ReferencesAllowed allowed after.core) ∧
    FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
    ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held bucket → FragmentAvoid after.core.representatives held fragment
-- Insert in SharedEagerReservation after ChildInputs, before end ActualChildInputs.
-- Add the cycle-free import MicroCFTA.SourceSynthesisProgramRolesNativeHeap.
-- Append inside SharedEagerReservation after ChildInputs.
-- Add the cycle-free import MicroCFTA.SourcePruningEnumerationIsolatedPending.
section ActualChildIsolation

private theorem child_inputs_isolated_pending
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing)
    (before after : Cached) (bucket : List Suspended) (fragment : Fragment) (queries : Queries)
    (held handle : Nat) (safe : Safe before.core)
    (isolated : EnumerationDischargeHistory.IsolatedPending held handle before.core)
    (inputs : Avoids before.core.representatives held bucket)
    (actual : ChildInputs formulas solver original metadata before bucket fragment reached queries after) :
    ChildInputs formulas solver original metadata before bucket fragment reached queries after ∧
      EnumerationDischargeHistory.IsolatedPending held handle after.core := by
  refine ⟨actual, ?_⟩
  obtain ⟨_next, _final, _post, _querySame, _packet, _growth, _origin,
    protection, referenceEffect, _fragmentBound, _fragmentPending, _fragmentAvoid⟩ := actual
  have inside : held < before.core.counter := by
    rw [safe.1.aligned]
    exact (List.getElem?_eq_some_iff.mp isolated.stored).1
  have protectedRoot : EnumerationDriver.Protected held before.core after.core :=
    protection held inside isolated.root inputs
  have allowedAfter : EnumerationReferences.ReferencesAllowed
      (fun target => ¬UnionFind.SameClass before.core.representatives held target) after.core :=
    referenceEffect _ isolated.incoming inputs
      (EnumerationReferences.fresh_separate before.core safe held inside)
  refine ⟨protectedRoot.root, protectedRoot.value.trans isolated.stored, ?_⟩
  intro value member sc listed same
  exact allowedAfter value member sc listed ((protectedRoot.classes sc.var).mp same)

/-- The actual finalizer retains the isolated boundary and child receipt. -/
private theorem finalized_child_inputs_isolated_pending
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing)
    (before middle after : Cached) (bucket : List Suspended) (fragment : Fragment)
    (queries : Queries) (target held handle fuel : Nat)
    (safe : Safe before.core)
    (isolated : EnumerationDischargeHistory.IsolatedPending held handle before.core)
    (avoids : Avoids before.core.representatives held bucket)
    (actual : ChildInputs formulas solver original metadata before bucket fragment reached queries middle)
    (different : target ≠ held)
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
      fuel target fragment middle = some after) :
    ChildInputs formulas solver original metadata before bucket fragment reached queries middle ∧
      EnumerationDischargeHistory.IsolatedPending held handle after.core
 := by
  obtain ⟨_, retained⟩ := child_inputs_isolated_pending formulas solver original reached metadata
    before middle bucket fragment queries held handle safe isolated avoids actual
  have preserved := EnumerationDischargeHistory.IsolatedPending.through_finalize
    reached.checked.native.machine.heap fuel target held handle fragment middle after
    retained different finalized
  exact ⟨actual, preserved⟩

end ActualChildIsolation

private theorem child_inputs_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing)
    (before after : Cached) (bucket : List Suspended) (fragment : Fragment) (queries : Queries)
    (safe : Safe before.core)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      original.checked.native.machine.heap before.core marked)
    (avoids : ∀ held, marked held → Avoids before.core.representatives held bucket)
    (actual : ChildInputs formulas solver original metadata before bucket fragment reached queries after) :
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      reached.checked.native.machine.heap after.core marked := by
  obtain ⟨_next, _final, post, _querySame, _packet, growth, _origin,
      protection, referenceEffect, _fragmentBound, _fragmentPending, _fragmentAvoid⟩ := actual
  have protects (held : Nat) (known : marked held) :
      EnumerationDriver.Protected held before.core after.core :=
    protection held (slots.bounded held known) (slots.roots held known) (avoids held known)
  have references (held : Nat) (known : marked held) :
      EnumerationReferences.ReferencesAllowed
        (fun target => ¬UnionFind.SameClass before.core.representatives held target) after.core :=
    referenceEffect _ (slots.incoming held known) (avoids held known)
      (EnumerationReferences.fresh_separate before.core safe held (slots.bounded held known))
  have carried := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
    original.checked.native.machine.heap reached.checked.native.machine.heap before.core marked
    post.effects.keeps slots
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro held known
    exact Nat.lt_of_lt_of_le (slots.bounded held known) growth
  · intro held known
    exact (protects held known).root
  · intro held known payload member sc listed same
    exact references held known payload member sc listed (((protects held known).classes sc.var).mp same)
  · intro held known
    obtain ⟨payload, stored, role⟩ := carried.stored held known
    exact ⟨payload, (protects held known).value.trans stored, role⟩
end ActualChildInputs

section ActualFallbackResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_fallback_resources_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (seed : Seed) (bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (bucket : List Suspended) (incoming : Node) (uv : Nat)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : bucket.length ≤ bound)
    (reserved : fallbackReserved bits bound ceiling admitted seed)
    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false)
    (yes : ∀ fragment reached saved after,
      ChildInputs formulas solver caller metadata before bucket fragment reached saved after →
      Fits (advance seed (bound + 1)).2 reached.checked →
      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound →
      admitted (ceiling + bound) (advance seed (bound + 1)) →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
          (finish uv outcome))
    (no : ∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
        (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
        (next : Inventory) (final : Memos),
      Post formulas solver next caller reached final → final.query = saved →
      Fits (advance seed (bound + 1)).2 reached.checked →
      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
      admitted (ceiling + bound) (advance seed (bound + 1)) →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
          (finish uv outcome)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        edgesOf bucket incoming caller before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
  have countLe : bucket.length + 1 ≤ bound + 1 := by omega
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, retained, eagerExact⟩ := fallback_complete_resources_cps seed formulas solver inventory caller memos
      metadata before checkEmpty edgesOf bucket incoming packet bounded pending available closed fits
      (reserved.1.prefix countLe) known fallback
  obtain ⟨headRun, post, query, growth, paths, storage, realized, counts, flags,
    origin, protects, references, pendingAfter, shape, actualFits, actualKnown⟩ := retained
  have paddedFits : Fits (advance seed (bound + 1)).2 afterCaller.checked :=
    actualFits.mono (SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed countLe)
  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
      afterCaller.checked.native.machine.heap := by
    have included : (advance seed (bucket.length + 1)).1 ⊆ (advance seed (bound + 1)).1 := by
      obtain ⟨extra, same⟩ := Nat.exists_eq_add_of_le countLe
      rw [same, advance_add seed (bucket.length + 1) extra]
      exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge
        (advance seed (bucket.length + 1)) extra
    intro key edge found
    exact included (actualKnown key edge found)
  have observed : ChildDispatch.run checkEmpty r n p h k bucket incoming caller before memos.query =
      ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
    simpa only [Nat.add_zero] using headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  have scalars := ChildDispatch.observed_scalar_bounds checkEmpty r n p h k bucket incoming
    caller before memos.query after (congrArg Prod.snd observed)
  have afterMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound :=
    Nat.le_trans scalars.2 (Nat.add_le_add mass bucketBound)
  have completed : ∃ fuel outcome,
      (∀ extra,
        (match raw with
        | [.ok (fragment, _returned)] => done (fuel + extra) fragment afterCaller savedQueries after
        | _ => stopped (fuel + extra) ((.ok (some raw), afterCaller, savedQueries, outer, waiting)) (some after)) = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
    rcases shape with rejected | ⟨fragment, singleton, afterSafe, fragmentBound, fragmentPending, fragmentAvoid⟩
    · obtain ⟨fuel, outcome, running, resources⟩ := no afterCaller savedQueries after outer waiting next final
        post query paddedFits paddedKnown reserved.2
      refine ⟨fuel, outcome, ?_, resources_outputs_post post resources⟩
      intro extra
      rw [rejected]
      exact running extra
    · have protectsEnumerated (held : Nat) (storedFragment : Fragment)
          (stored : before.core.values[held]? = some (.enumerated storedFragment)) :
          EnumerationDriver.Protected held before.core after.core := by
        obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment stored
        exact protects held inside root (pending held storedFragment stored)
      have afterPacket : Packet formulas solver next afterCaller final metadata after := by
        refine ⟨post.context, afterSafe, pendingAfter packet.pending,
          ⟨afterRoots, paths, storage, realized, counts, flags⟩, ?_, ?_⟩
        · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
          obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core after.core
            afterSafe level frontier oldOrder origin protectsEnumerated
          exact ⟨nextLevel, frontier, afterOrder⟩
        · intro group member entry listed
          exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
      have inputs : ChildInputs formulas solver caller metadata before bucket fragment afterCaller savedQueries after :=
        ⟨next, final, post, query, afterPacket, growth, origin, protects,
          (fun allowed valid supplied _future => references allowed valid supplied),
          fragmentBound, fragmentPending, fragmentAvoid⟩
      obtain ⟨fuel, outcome, running, resources⟩ := yes fragment afterCaller savedQueries after inputs
        paddedFits paddedKnown afterMass reserved.2
      refine ⟨fuel, outcome, ?_, resources_outputs_post post resources⟩
      intro extra
      rw [singleton]
      exact running extra
  obtain ⟨callbackFuel, outcome, consumeRun, resources⟩ := completed
  let total := r + n + p + h + k + callbackFuel
  refine ⟨total, outcome, ?_, resources⟩
  intro extra
  let work := total + extra
  have rle : r ≤ work := by dsimp [work, total]; omega
  have nle : n ≤ work := by dsimp [work, total]; omega
  have kle : k ≤ work := by dsimp [work, total]; omega
  have re : r + (work - r) = work := by omega
  have ne : n + (work - n) = work := by omega
  have ke : k + (work - k) = work := by omega
  have head := eagerExact (work - r) (work - n) work work (work - k)
    (by dsimp [work, total]; omega) (by dsimp [work, total]; omega) (done work) (stopped work)
  simp only [re, ne, ke] at head
  change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work
    edgesOf bucket incoming caller before memos.query (done work) (stopped work) = outcome
  rw [head]
  have actual := consumeRun (r + n + p + h + k + extra)
  have same : callbackFuel + (r + n + p + h + k + extra) = work := by dsimp [work, total]; omega
  simpa only [same] using actual

private theorem eager_fallback_resources
    (seed : Seed) (bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (bucket : List Suspended) (incoming : Node) (uv : Nat)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : bucket.length ≤ bound)
    (reserved : fallbackReserved bits bound ceiling admitted seed)
    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false)
    (yes : ∀ fragment reached saved after,
      ChildInputs formulas solver caller metadata before bucket fragment reached saved after →
      Fits (advance seed (bound + 1)).2 reached.checked →
      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound →
      admitted (ceiling + bound) (advance seed (bound + 1)) →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
        OutcomeResources formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
          (finish uv outcome))
    (no : ∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
        (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
        (next : Inventory) (final : Memos),
      Post formulas solver next caller reached final → final.query = saved →
      Fits (advance seed (bound + 1)).2 reached.checked →
      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
      admitted (ceiling + bound) (advance seed (bound + 1)) →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResources formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
          (finish uv outcome)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        edgesOf bucket incoming caller before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResources formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
  simpa only [resources_outputs_true_iff] using
    (eager_fallback_resources_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) seed bound ceiling continuation admitted formulas solver inventory caller memos metadata before checkEmpty edgesOf bucket incoming uv done stopped packet bounded pending available closed fits known mass bucketBound reserved fallback
      (by simpa only [resources_outputs_true_iff] using yes)
      (by simpa only [resources_outputs_true_iff] using no))
end ActualFallbackResources

section ActualTupleInputs
variable [DecidableEq (EdgeKey Symbol Constraint)]

private def TupleInputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
    (inputs : List (Node × List Suspended)) (fragments : List Fragment)
    (reached : Caller (bits + 2)) (queries : Queries) (after : Cached) : Prop :=
  ∃ (next : Inventory) (final : Memos),
    Post formulas solver next original reached final ∧ final.query = queries ∧
    Packet formulas solver next reached final metadata after ∧ before.core.counter ≤ after.core.counter ∧
    EnumeratedOrigin before.core after.core ∧
    (∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
      EnumerationDriver.Protected held before.core after.core) ∧
    (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      (∀ child bucket, (child, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
      EnumerationDriver.Protected held before.core after.core) ∧
    (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
      (∀ child bucket, (child, bucket) ∈ inputs → EnumerationReferences.InputsAllowed allowed bucket) →
      (∀ uv, before.core.counter ≤ uv → allowed uv) →
      EnumerationReferences.ReferencesAllowed allowed after.core) ∧
    (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
    ∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
      ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        (∀ child bucket, (child, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
        FragmentAvoid after.core.representatives held fragment

private theorem child_then_tuple_inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (packet : Packet formulas solver inventory caller memos metadata before)
    (genuine : ∀ child retained, (child, retained) ∈ (incoming, bucket) :: rest →
      Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained)
    (fragment : Fragment) (middleCaller : Caller (bits + 2)) (middleQueries : Queries) (middle : Cached)
    (head : ChildInputs formulas solver caller metadata before bucket fragment middleCaller middleQueries middle) :
    (∀ child retained, (child, retained) ∈ rest →
      Available middleCaller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ retained, sc.var < middle.core.counter) ∧ InputsPending middle.core retained) ∧
    ∀ fragments afterCaller saved after,
      TupleInputs formulas solver middleCaller metadata middle rest fragments afterCaller saved after →
      TupleInputs formulas solver caller metadata before ((incoming, bucket) :: rest)
        (fragment :: fragments) afterCaller saved after
    := by
  obtain ⟨_middleInventory, _middleMemos, headPost, _headQueries, middlePacket,
    growth, headOrigin, headProtected, headReferences, fragmentBound, fragmentPending, fragmentSeparate⟩ := head
  have pending : InputsPending before.core bucket := (genuine incoming bucket (by simp)).2.2.2
  have protects : ∀ held storedFragment, before.core.values[held]? = some (.enumerated storedFragment) →
      EnumerationDriver.Protected held before.core middle.core := by
    intro held storedFragment stored
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment stored
    exact headProtected held inside root (pending held storedFragment stored)
  constructor
  · intro child retained member
    obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
      genuine child retained (List.mem_cons_of_mem _ member)
    refine ⟨headPost.effects.keeps.available child childAvailable, childClosed,
      fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
    intro held storedFragment stored
    have old := headOrigin held storedFragment stored
    exact (protects held storedFragment old).avoids retained (childPending held storedFragment old)
  · intro fragments afterCaller saved after tail
    obtain ⟨next, final, tailPost, querySame, afterPacket, tailGrowth, tailOrigin,
      tailProtected, tailRootsProtected, tailReferences, tailBounds, fragmentHistory⟩ := tail
    refine ⟨next, final, headPost.trans tailPost, querySame, afterPacket, Nat.le_trans growth tailGrowth,
      headOrigin.trans tailOrigin, ?_, ?_, ?_, ?_, ?_⟩
    · intro held storedFragment stored
      have first := protects held storedFragment stored
      have middleStored : middle.core.values[held]? = some (.enumerated storedFragment) := first.value.trans stored
      exact first.trans (tailProtected held storedFragment middleStored)
    · intro held inside root avoids
      have first := headProtected held inside root (avoids incoming bucket (by simp))
      apply first.trans
      apply tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root
      intro child retained member
      exact first.avoids retained (avoids child retained (List.mem_cons_of_mem _ member))
    · intro allowed valid allowedInputs future
      apply tailReferences allowed (headReferences allowed valid (allowedInputs incoming bucket (by simp)) future)
      · intro child retained member
        exact allowedInputs child retained (List.mem_cons_of_mem _ member)
      · intro uv inside
        exact future uv (Nat.le_trans growth inside)
    · intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact fragmentBound_mono _ _ tailGrowth _ fragmentBound
      · exact tailBounds child member
    · intro child member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨pendingFragment_preserved middle.core after.core middlePacket.safe afterPacket.safe
          tailGrowth child fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
        intro held inside root avoids
        have first := headProtected held inside root (avoids incoming bucket (by simp))
        have last := tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root (by
          intro child retained member
          exact first.avoids retained (avoids child retained (List.mem_cons_of_mem _ member)))
        exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held child
          last.classes).mpr (fragmentSeparate held inside root (avoids incoming bucket (by simp)))
      · obtain ⟨childPending, childSeparate⟩ := fragmentHistory child member
        refine ⟨childPending, ?_⟩
        intro held inside root avoids
        have first := headProtected held inside root (avoids incoming bucket (by simp))
        apply childSeparate held (Nat.lt_of_lt_of_le inside growth) first.root
        intro child retained member
        exact first.avoids retained (avoids child retained (List.mem_cons_of_mem _ member))

private theorem tuple_inputs_nil
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (packet : Packet formulas solver inventory caller memos metadata before) :
    TupleInputs formulas solver caller metadata before [] [] caller memos.query before
    := by
  refine ⟨inventory, memos, Post.refl packet.context, rfl, packet, Nat.le_refl _, .refl _, ?_, ?_,
    (fun _ valid _ _ => valid), ?_, ?_⟩
  · intro held fragment stored
    exact EnumerationDriver.Protected.refl held before.core (enumerated_root before.core packet.safe held fragment stored).2
  · intro held _ root _
    exact EnumerationDriver.Protected.refl held before.core root
  · intro fragment member
    cases member
  · intro fragment member
    cases member

end ActualTupleInputs

section ActualConsumers
variable [DecidableEq (EdgeKey Symbol Constraint)]

private def ChildConsumersWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragment reached saved after,
    ChildInputs formulas solver original metadata before bucket fragment reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome))

private def ChildConsumers
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragment reached saved after,
    ChildInputs formulas solver original metadata before bucket fragment reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome))
end ActualConsumers

section ActualHeightBase
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def EagerChildCompleteWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (bucket : List Suspended) (incoming : Node) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    Available captured incoming → SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    incoming.free = [] → (∀ sc ∈ bucket, sc.var < before.core.counter) → InputsPending before.core bucket →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → bucket.length ≤ bound →
    MergedOrdinaryHeight.height incoming ≤ height →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    nodeReserved bits limit own height bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ChildConsumersWithOutputs outputOK formulas solver caller metadata before bucket uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller
        before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (nodePlan limit own height bound ceiling continuation seed) (finish uv outcome)

private def EagerChildComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (bucket : List Suspended) (incoming : Node) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    Available captured incoming → SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    incoming.free = [] → (∀ sc ∈ bucket, sc.var < before.core.counter) → InputsPending before.core bucket →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → bucket.length ≤ bound →
    MergedOrdinaryHeight.height incoming ≤ height →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    nodeReserved bits limit own height bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ChildConsumers formulas solver caller metadata before bucket uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller
        before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResources formulas solver caller
        (nodePlan limit own height bound ceiling continuation seed) (finish uv outcome)

private theorem eager_child_height_zero_complete_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own 0 formulas solver := by
  intro inventory caller memos metadata before seed bound ceiling bucket incoming uv continuation admitted done stopped
    packet fits known capturedAvailable kept closed bounded pending mass bucketBound heightBound
    _shapes _selectionMembers _selectionLength reserved _growth consumers
  have fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false := by
    cases incoming with
    | empty => rfl
    | reference name => rfl
    | node entry rows depth free =>
        simp only [MergedOrdinaryHeight.height] at heightBound
        omega
    | union entry members depth free => rfl
    | mu entry body depth ordinary => rfl
  exact eager_fallback_resources_with_outputs outputOK seed bound ceiling continuation admitted formulas solver inventory caller memos metadata
    before checkEmpty edgesOf bucket incoming uv done stopped packet bounded pending
    (kept.available incoming capturedAvailable) closed fits known mass bucketBound reserved fallback
    (fun fragment reached saved after inputs bounded known mass accepted =>
      consumers.1 fragment reached saved after inputs (advance seed (bound + 1)) (ceiling + bound)
        bounded known mass accepted)
    (fun reached saved after outer waiting next final post query bounded known accepted =>
      consumers.2 reached saved after outer waiting next final post query (advance seed (bound + 1)) (ceiling + bound)
        bounded known accepted)

private theorem eager_child_height_zero_complete
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own 0 formulas solver := by
  simpa only [EagerChildCompleteWithOutputs, EagerChildComplete, ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using
    (eager_child_height_zero_complete_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own formulas solver)
end ActualHeightBase

section ActualTupleConsumers
variable [DecidableEq (EdgeKey Symbol Constraint)]

private def TupleConsumersWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
    (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragments reached saved after,
    TupleInputs formulas solver original metadata before inputs fragments reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragments reached saved after = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (completed : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) completed ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome))

private def TupleConsumers
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
    (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragments reached saved after,
    TupleInputs formulas solver original metadata before inputs fragments reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragments reached saved after = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (completed : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) completed ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome))
end ActualTupleConsumers

section ActualPlannedTuple
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def EagerTupleCompleteWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → inputs.length ≤ count →
    (∀ child bucket, (child, bucket) ∈ inputs →
      Available captured child ∧ child.free = [] ∧ MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
        (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    TupleConsumersWithOutputs outputOK formulas solver caller metadata before inputs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) inputs caller before memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome)

private def EagerTupleComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → inputs.length ≤ count →
    (∀ child bucket, (child, bucket) ∈ inputs →
      Available captured child ∧ child.free = [] ∧ MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
        (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    TupleConsumers formulas solver caller metadata before inputs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) inputs caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome)

private theorem eager_tuple_nil_resources_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (uv : Nat)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before) (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed)
    (consumers : TupleConsumersWithOutputs outputOK formulas solver caller metadata before [] uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
  let visit : Nat → Visitor := fun fuel =>
    SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty fuel fuel fuel fuel fuel edgesOf
  exact tuple_nil_reserved_resources_with_outputs outputOK limit own height count bound ceiling continuation admitted growth seed formulas solver
    caller memos before uv visit done stopped fits known mass reserved (fun retained current bounded supported mass accepted =>
      consumers.1 [] caller memos.query before
        (tuple_inputs_nil formulas solver inventory caller memos metadata before packet)
        current retained bounded supported mass accepted)

private theorem eager_tuple_nil_resources
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (uv : Nat)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before) (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed)
    (consumers : TupleConsumers formulas solver caller metadata before [] uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
  simpa only [resources_outputs_true_iff] using
    (eager_tuple_nil_resources_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf limit own height count bound ceiling continuation admitted growth seed formulas solver inventory caller memos metadata before uv done stopped packet fits known mass reserved
      (by simpa only [TupleConsumersWithOutputs, TupleConsumers, resources_outputs_true_iff] using consumers))

private theorem eager_tuple_complete_of_child_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerTupleCompleteWithOutputs outputOK (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling inputs uv continuation admitted done stopped
        packet fits known kept mass length _genuine _shapes _selectionMembers _selectionLength reserved growth consumers
      cases inputs with
      | nil =>
          exact eager_tuple_nil_resources_with_outputs outputOK checkEmpty edgesOf limit own height 0 bound ceiling continuation admitted growth
            seed formulas solver inventory caller memos metadata before uv done stopped packet fits known mass reserved consumers
      | cons first rest => simp only [List.length_cons] at length; omega
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling inputs uv continuation admitted done stopped
        packet fits known kept mass length genuine shapes selectionMembers selectionLength reserved growth consumers
      cases inputs with
      | nil =>
          exact eager_tuple_nil_resources_with_outputs outputOK checkEmpty edgesOf limit own height (count + 1) bound ceiling continuation admitted growth
            seed formulas solver inventory caller memos metadata before uv done stopped packet fits known mass reserved consumers
      | cons input rest =>
          rcases input with ⟨incoming, bucket⟩
          obtain ⟨available, closed, ranked, bucketBound, bounded, pending⟩ := genuine incoming bucket (by simp)
          let tailPlan := fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current
          let tailAdmitted := fun retained current => tupleReserved (nodePlan limit own height)
            (nodeReserved bits limit own height) count bound retained continuation admitted current
          let yes : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
            fun fuel fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty fuel fuel fuel fuel fuel edgesOf)
              (fun fragments => done fuel (fragment :: fragments))
              (fun completed => stopped fuel (fragment :: completed)) rest reached after saved
          let no : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
            fun fuel observation candidate => stopped fuel [] observation candidate
          have tailGrowth : ∀ retained current, Le current.2 (tailPlan retained current).2 ∧
              current.1 ⊆ (tailPlan retained current).1 := by
            intro retained current
            exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
              count bound retained continuation growth current
          have headConsumers : ChildConsumersWithOutputs outputOK formulas solver caller metadata before bucket uv tailPlan tailAdmitted yes no := by
            constructor
            · intro fragment reached saved after head current retained fitted supported afterMass admittedAfter
              have currentGenuine : ∀ value retainedBucket, (value, retainedBucket) ∈ (incoming, bucket) :: rest →
                  Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
                  (∀ sc ∈ retainedBucket, sc.var < before.core.counter) ∧ InputsPending before.core retainedBucket := by
                intro value bucket member
                obtain ⟨oldAvailable, closed, _ranked, _width, bounded, pending⟩ := genuine value bucket member
                exact ⟨kept.available value oldAvailable, closed, bounded, pending⟩
              have combined := child_then_tuple_inputs formulas solver inventory caller memos metadata before incoming bucket rest
                packet currentGenuine fragment reached saved after head
              obtain ⟨next, final, post, query, afterPacket, _growth, _origin, _protected,
                _references, _bounded, _pending, _avoids⟩ := head
              have tailGenuine : ∀ value bucket, (value, bucket) ∈ rest →
                  Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧ bucket.length ≤ bound ∧
                    (∀ sc ∈ bucket, sc.var < after.core.counter) ∧ InputsPending after.core bucket := by
                intro value bucket member
                obtain ⟨oldAvailable, closed, ranked, width, _bounded, _pending⟩ :=
                  genuine value bucket (List.mem_cons_of_mem _ member)
                obtain ⟨_available, _closed, bounded, pending⟩ := combined.1 value bucket member
                exact ⟨oldAvailable, closed, ranked, width, bounded, pending⟩
              let tailDone : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
                fun fuel fragments => done fuel (fragment :: fragments)
              let tailStopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
                fun fuel completed => stopped fuel (fragment :: completed)
              have tailConsumers : TupleConsumersWithOutputs outputOK formulas solver reached metadata after rest uv continuation admitted
                  tailDone tailStopped := by
                constructor
                · intro fragments finalCaller queries finished history entry ceiling fitted supported mass accepted
                  exact consumers.1 (fragment :: fragments) finalCaller queries finished
                    (combined.2 fragments finalCaller queries finished history) entry ceiling fitted supported mass accepted
                · intro completed finalCaller queries finished outer waiting inventory memos later query
                    entry ceiling fitted supported accepted
                  exact consumers.2 (fragment :: completed) finalCaller queries finished outer waiting inventory memos
                    (post.trans later) query entry ceiling fitted supported accepted
              have tailLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              obtain ⟨fuel, outcome, running, resources⟩ := ih next reached final metadata after current bound retained rest uv
                continuation admitted tailDone tailStopped afterPacket fitted supported (kept.trans post.effects.keeps)
                afterMass tailLength tailGenuine shapes selectionMembers selectionLength admittedAfter growth tailConsumers
              refine ⟨fuel, outcome, ?_, resources⟩
              intro extra
              simpa only [yes, tailDone, tailStopped, query] using running extra
            · intro reached saved after outer waiting next final post query current retained fitted supported accepted
              let entry := advance current (count * (bound + 1))
              have entryFits : Fits entry.2 reached.checked := fitted.mono
                (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge current (count * (bound + 1)))
              have entryKnown : Heap (fun guard => guard ∈ entry.1) reached.checked.native.machine.heap := by
                intro key edge found
                exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge current
                  (count * (bound + 1)) (supported key edge found)
              have entryAdmitted : admitted (retained + count * bound) entry :=
                tupleReserved_first_callback bits limit own height count bound retained continuation admitted current accepted
              obtain ⟨fuel, outcome, running, resources⟩ := consumers.2 [] reached saved after outer waiting next final
                post query entry (retained + count * bound) entryFits entryKnown entryAdmitted
              have included := first_callback_le_tuple_of_growth limit own height count bound retained continuation growth current
              exact ⟨fuel, outcome, running, resources_outputs_mono included.1 included.2 resources⟩
          obtain ⟨fuel, outcome, running, resources⟩ := child inventory caller memos metadata before seed bound ceiling bucket
            incoming uv tailPlan tailAdmitted yes no packet fits known available kept closed bounded pending mass bucketBound
            ranked shapes selectionMembers selectionLength reserved tailGrowth headConsumers
          refine ⟨fuel, outcome, ?_, resources⟩
          intro extra
          change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller before
            memos.query (yes (fuel + extra)) (no (fuel + extra)) = outcome
          exact running extra

private theorem eager_tuple_complete_of_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerTupleComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
  simpa only [EagerTupleCompleteWithOutputs, EagerTupleComplete, TupleConsumersWithOutputs, TupleConsumers, resources_outputs_true_iff] using
    (eager_tuple_complete_of_child_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver
      (by simpa only [EagerChildCompleteWithOutputs, EagerChildComplete, ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using child) count)
end ActualPlannedTuple

section ActualOwnTupleInputs
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem own_tuple_child_inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller (bits + 2)) (metadata : Metadata Typing) (before own : Cached)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (tries : List EqualityTrie.Trie)
    (residual : Option Constraint)
    (ownCore : own.core = suspendedState tries.length before.core)
    (ownCounter : own.core.counter = before.core.counter + tries.length)
    (ownProtects : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held scs →
      EnumerationDriver.Protected held before.core own.core ∧
        ∀ incoming bucket, (incoming, bucket) ∈
          SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
          Avoids own.core.representatives held bucket)
    (fragments : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (history : TupleInputs formulas solver caller metadata own
      (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries)
      fragments reached saved after) :
    ChildInputs formulas solver caller metadata before scs (.node edge.entry.key.symbol fragments) reached saved
      (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
    := by
  obtain ⟨next, final, post, querySame, afterPacket, growth, origin, _enumProtects,
    rootsProtects, references, fragmentBounds, fragmentHistory⟩ := history
  have ownGrowth : before.core.counter ≤ own.core.counter := by
    rw [ownCounter]
    exact Nat.le_add_right _ _
  have ownOrigin : EnumeratedOrigin before.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length before.core
  have nodeBound : FragmentBound after.core.counter (.node edge.entry.key.symbol fragments) := by
    have listBound : ∀ pieces : List Fragment,
        (∀ child ∈ pieces, FragmentBound after.core.counter child) → FragmentsBound after.core.counter pieces := by
      intro pieces
      induction pieces with
      | nil => intro _; trivial
      | cons first rest ih =>
        intro bounded
        exact ⟨bounded first (by simp), ih (fun child member => bounded child (List.mem_cons_of_mem _ member))⟩
    exact listBound fragments fragmentBounds
  let fragment : Fragment := .node edge.entry.key.symbol fragments
  let finished := SelectedEdge.finish residual fragment after
  have finishedSafe : Safe finished.core := SelectedEdge.finish_safe residual fragment after afterPacket.safe nodeBound
  have finishedPacket : Packet formulas solver next reached final metadata finished := by
    obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := afterPacket.valid
    obtain ⟨level, frontier, ordered⟩ := afterPacket.ordered
    exact ⟨afterPacket.context, finishedSafe, afterPacket.pending,
      ⟨roots, paths, finishedSafe.1, realized, counts, flags⟩,
      ⟨level, frontier, ordered.classes, ordered.expanded, ordered.pending⟩, afterPacket.bounded⟩
  refine ⟨next, final, post, querySame, finishedPacket, Nat.le_trans ownGrowth growth,
    ownOrigin.trans origin, ?_, ?_, nodeBound, ?_, ?_⟩
  · intro held inside root avoids
    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
    have childFrame := rootsProtects held (Nat.lt_of_lt_of_le inside ownGrowth) frame.root avoidsChildren
    exact frame.trans (childFrame.trans (SelectedEdge.finish_protected residual fragment after held childFrame.root))
  · intro allowed valid inherited future
    have ownAllowed : EnumerationReferences.ReferencesAllowed allowed own.core := by
      rw [ownCore]
      exact EnumerationReferences.suspension_allowed allowed tries.length before.core valid
    have freshAllowed : EnumerationReferences.InputsAllowed allowed (suspendedVars before.core.counter tries) :=
      EnumerationReferences.suspended_allowed allowed before.core.counter before.core.counter tries (Nat.le_refl _) future
    apply references allowed ownAllowed
    · intro child bucket member
      obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp member
      cases pairSame
      intro sc listed
      rcases List.mem_append.mp listed with inheritedMember | freshMember
      · exact EnumerationReferences.descend_allowed allowed scs indexed.2 inherited sc inheritedMember
      · exact EnumerationReferences.descend_allowed allowed (suspendedVars before.core.counter tries)
          indexed.2 freshAllowed sc freshMember
    · intro uv lower
      exact future uv (Nat.le_trans ownGrowth lower)
  · exact pendingFragment_node after.core edge.entry.key.symbol fragments
      (fun child member => (fragmentHistory child member).1)
  · intro held inside root avoids uv hole
    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
    change HasHole (.node edge.entry.key.symbol fragments) uv at hole
    cases hole with
    | child _ _ child _ member below =>
      exact (fragmentHistory child member).2 held (Nat.lt_of_lt_of_le inside ownGrowth)
        frame.root avoidsChildren uv below

end ActualOwnTupleInputs

section ActualSelectedResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_selected_resources_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (consumers : ChildConsumersWithOutputs outputOK formulas solver caller metadata before scs uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitSelected
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query)
        scs edge caller before memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome) := by
  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
    limit (bound + own) ceiling continuation growth seed
  have planFits := fits.mono planGrowth.1
  have planKnown : Heap
      (fun guard => guard ∈ (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed).1)
      caller.checked.native.machine.heap := by
    intro key edge found
    exact planGrowth.2 (known key edge found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        let outcome : Fold := .stopped [] [] (.edge (some .unhandled) (caller, memos.query))
        refine ⟨0, outcome, ?_, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
            SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
          rfl
        · constructor
          · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, .inr rfl, ?_⟩
            intro output member
            cases member
          · intro output member
            cases member
    | some fields =>
        rcases fields with ⟨tries, residual⟩
        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, lower, reducing⟩ :=
          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
        obtain ⟨_prepared, _middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, middleProtects⟩ := ownReceipt
        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
        have edgeBounds := (shapes parentEntry rows depth free available).2 edge selected
        have triesBound := edgeBounds.2 tries residual projected
        have inputLength : inputs.length ≤ limit := by
          simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using edgeBounds.1
        have inputFacts : ∀ value bucket, (value, bucket) ∈ inputs →
            Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
              bucket.length ≤ bound + own ∧ (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value bucket member
          obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine value bucket member
          have childRank := lower value bucket member
          obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
          cases same
          have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
          have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
            (suspendedVars before.core.counter tries)
          rw [SourcePruningEnumerationCostBounds.suspended_length] at added
          refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
            ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, by omega, ?_, childBounded, childPending⟩
          simp only [List.length_append]
          omega
        have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling := by
          rw [middleMass]
          exact mass
        let yes : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
          fun fuel fragments reached saved after =>
            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
              (.complete (.node edge.entry.key.symbol fragments) reached saved
                (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after))
        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
          fun fuel completed observation candidate =>
            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
              (.stopped completed observation candidate)
        have tupleConsumers : TupleConsumersWithOutputs outputOK formulas solver caller metadata middle inputs uv continuation admitted yes no := by
          constructor
          · intro fragments reached saved after history current retained fitted supported afterMass accepted
            have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
              middleCore middleCounter middleProtects fragments reached saved after history
            obtain ⟨fuel, outcome, running, resources⟩ := consumers.1 (.node edge.entry.key.symbol fragments)
              reached saved (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
              data current retained fitted supported afterMass accepted
            let receipt : SelectedEdge.Result (bits + 2) := .complete (.node edge.entry.key.symbol fragments)
              reached saved (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
            let result : Fold := match outcome with
              | .complete processed outputs finalCaller finalQueries => .complete (receipt :: processed) outputs finalCaller finalQueries
              | .stopped processed outputs stop => .stopped (receipt :: processed) outputs stop
            refine ⟨fuel, result, ?_, ?_⟩
            · intro extra
              change SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query
                (.complete (.node edge.entry.key.symbol fragments) reached saved
                  (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)) = result
              rw [SourcePruningEnumerationSharedEagerChildren.consume_complete, running extra]
              cases outcome <;> rfl
            · cases outcome <;> exact resources
          · intro completed reached saved after outer waiting next final post query current retained fitted supported _accepted
            let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
              ((.ok (some []), reached, saved, outer, waiting)) (some after)
            let outcome : Fold := .complete [receipt] [] reached saved
            have resources : OutcomeResourcesWithOutputs outputOK formulas solver reached current (finish uv outcome) := by
              constructor
              · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                intro output member
                cases member
              · intro output member
                cases member
            have enlarged := growth retained current
            exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
        have tuple := eager_tuple_complete_of_child_with_outputs outputOK (Typing := Typing) (bits := bits)
          checkEmpty edgesOf captured limit own height formulas solver child limit
        obtain ⟨fuel, outcome, running, resources⟩ := tuple inventory caller memos metadata middle seed
          (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
          inputFacts shapes selectionMembers selectionLength reserved growth tupleConsumers
        refine ⟨fuel, outcome, ?_, resources⟩
        intro extra
        rw [reducing]
        exact running extra
  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
    refine ⟨0, outcome, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
        SourcePruningEnumerationCachedOwn.prepare, allowed]
      rfl
    · constructor
      · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
        intro output member
        cases member
      · intro output member
        cases member

private theorem eager_selected_resources
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (consumers : ChildConsumers formulas solver caller metadata before scs uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitSelected
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query)
        scs edge caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome) := by
  simpa only [resources_outputs_true_iff] using
    (eager_selected_resources_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver
      (by simpa only [EagerChildCompleteWithOutputs, EagerChildComplete, ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using child) inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped packet fits known kept mass bucketBound parentEntry rows depth free available closed ranked edge selected bounded pending shapes selectionMembers selectionLength reserved growth
      (by simpa only [ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using consumers))
end ActualSelectedResources

section ActualRowsConsumers
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem child_consumers_post_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original middle : Caller (bits + 2)) (next : Inventory) (final : Memos)
    (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (earlier : Post formulas solver next original middle final)
    (consumers : ChildConsumersWithOutputs outputOK formulas solver original metadata before bucket uv continuation admitted done stopped) :
    ChildConsumersWithOutputs outputOK formulas solver middle metadata before bucket uv continuation admitted done stopped := by
  constructor
  · intro fragment reached saved after data current retained fitted supported mass accepted
    obtain ⟨next, final, post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩ := data
    exact consumers.1 fragment reached saved after
      ⟨next, final, earlier.trans post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩
      current retained fitted supported mass accepted
  · intro reached saved after outer waiting next final post query current retained fitted supported accepted
    exact consumers.2 reached saved after outer waiting next final (earlier.trans post) query
      current retained fitted supported accepted

private theorem child_consumers_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original middle : Caller (bits + 2)) (next : Inventory) (final : Memos)
    (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (earlier : Post formulas solver next original middle final)
    (consumers : ChildConsumers formulas solver original metadata before bucket uv continuation admitted done stopped) :
    ChildConsumers formulas solver middle metadata before bucket uv continuation admitted done stopped := by
  simpa only [ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using
    (child_consumers_post_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) formulas solver original middle next final metadata before bucket uv continuation admitted done stopped earlier
      (by simpa only [ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using consumers))
end ActualRowsConsumers

section ActualRowsResources
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def EagerRowsCompleteWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed index)) →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ChildConsumersWithOutputs outputOK formulas solver caller metadata before scs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) reached saved)
          scs edge reached cached saved) before alternatives caller memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed count) (finish uv outcome)

private def EagerRowsComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed index)) →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ChildConsumers formulas solver caller metadata before scs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) reached saved)
          scs edge reached cached saved) before alternatives caller memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed count) (finish uv outcome)

private theorem eager_rows_complete_of_child_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerRowsCompleteWithOutputs outputOK (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped
        packet fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending
        alternatives length _selected _shapes _selectionMembers _selectionLength _reserved growth _consumers
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl,
            fun _ member => by cases member⟩, fun _ member => by cases member⟩
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped
        packet fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending
        alternatives length selected shapes selectionMembers selectionLength reserved growth consumers
      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      cases alternatives with
      | nil =>
          have enlarged := iterate_ge row rowGrowth seed (count + 1)
          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
              caller.checked.native.machine.heap := by
            intro key edge found
            exact enlarged.2 (known key edge found)
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
            supported, rfl, rfl, fun _ member => by cases member⟩, fun _ member => by cases member⟩
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_selected_resources_with_outputs outputOK
            checkEmpty edgesOf captured limit own height formulas solver child inventory caller memos metadata before seed
            bound ceiling scs uv continuation admitted done stopped packet fits known kept mass bucketBound
            parentEntry rows depth free available closed ranked edge (selected edge (by simp)) bounded pending
            shapes selectionMembers selectionLength firstReserved growth consumers
          have farther := iterate_ge row rowGrowth (row seed) count
          cases headOutcome with
          | stopped processed outputs current =>
              refine ⟨headFuel, .stopped processed outputs current, ?_, resources_outputs_mono farther.1 farther.2 headResources⟩
              intro extra
              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
          | complete processed outputs reached saved =>
              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, _outputResources⟩ :=
                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources.1
              have laterReserved : ∀ index, index < count →
                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
                intro index inside
                exact reserved (index + 1) (by omega)
              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              have reachedConsumers := child_consumers_post_with_outputs outputOK formulas solver caller reached next final metadata before scs uv
                continuation admitted done stopped post consumers
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
                bound ceiling scs uv continuation admitted done stopped reachedPacket reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved growth reachedConsumers
              let result : Fold := match (generalizing := false) tailOutcome with
                | .complete later remaining finalCaller finalQueries =>
                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
              · intro extra
                have headAt := headRunning (tailFuel + extra)
                have tailAt := tailRunning (headFuel + extra)
                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
                rw [hs] at headAt
                rw [ts, query] at tailAt
                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
                dsimp only
                rw [tailAt]
                cases tailOutcome <;> rfl
              · simpa only [SourcePruningEnumerationFiniteReservation.iterate_succ, row, result] using
                  (resources_outputs_append uv processed outputs tailOutcome post farther.1 farther.2
                    (by simpa only [query, finish, row] using headResources) tailResources)

private theorem eager_rows_complete_of_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerRowsComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
  simpa only [EagerRowsCompleteWithOutputs, EagerRowsComplete, ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using
    (eager_rows_complete_of_child_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver
      (by simpa only [EagerChildCompleteWithOutputs, EagerChildComplete, ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using child) count)
end ActualRowsResources

section ActualVisitorCongruence

private theorem children_members_congr (left right : Visitor) (inputs : List (Node × List Suspended)) :
    (∀ child bucket, (child, bucket) ∈ inputs → ∀ caller before queries done stopped,
      left bucket child caller before queries done stopped = right bucket child caller before queries done stopped) →
    ∀ done stopped caller before queries,
      SourcePruningEnumerationSharedChildVisitors.visitChildren left done stopped inputs caller before queries =
        SourcePruningEnumerationSharedChildVisitors.visitChildren right done stopped inputs caller before queries := by
  induction inputs with
  | nil => intro _ _ _ _ _ _; rfl
  | cons input rest ih =>
      rcases input with ⟨child, bucket⟩
      intro same done stopped caller before queries
      simp only [SourcePruningEnumerationSharedChildVisitors.visitChildren]
      rw [same child bucket (by simp)]
      apply congrArg (fun yes => right bucket child caller before queries yes
        (fun observation candidate => stopped [] observation candidate))
      funext fragment reached saved after
      exact ih (fun value retained member => same value retained (List.mem_cons_of_mem _ member))
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) reached after saved

private theorem scan_members_congr
    (left right : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold)
    (before : Cached) (rows : List (EdgeValue Symbol Constraint))
    (same : ∀ edge ∈ rows, ∀ caller queries, left edge caller queries before = right edge caller queries before)
    (caller : Caller (bits + 2)) (queries : Queries) :
    SourcePruningEnumerationSharedBranching.scan left before rows caller queries =
      SourcePruningEnumerationSharedBranching.scan right before rows caller queries := by
  induction rows generalizing caller queries with
  | nil => rfl
  | cons edge rest ih =>
      simp only [SourcePruningEnumerationSharedBranching.scan, same edge List.mem_cons_self caller queries]
      cases observed : right edge caller queries before with
      | stopped processed outputs current => rfl
      | complete processed outputs reached saved =>
          simp only [ih (fun chosen member => same chosen (List.mem_cons_of_mem _ member)) reached saved]

end ActualVisitorCongruence

section ActualPreparedGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem selected_guarded_eq
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows) (scs : List Suspended)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (consume : SelectedEdge.Result (bits + 2) → Fold) :
    SourcePruningEnumerationSharedChildVisitors.visitSelected
      (fun bucket child current cache memos yes no =>
        if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free) then
          SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf
            bucket child current cache memos yes no
        else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k
          bucket child current cache memos yes no)
      consume scs edge caller before queries =
    SourcePruningEnumerationSharedChildVisitors.visitSelected
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf)
      consume scs edge caller before queries := by
  cases prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
  | some results =>
      cases results with
      | nil => simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
      | cons first rest =>
          cases rest with
          | cons second rest => simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
          | nil =>
              rcases first with ⟨⟨symbol, staged, residual⟩, middle⟩
              simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
              apply children_members_congr
              intro child bucket member current cache memos yes no
              obtain ⟨_tries, _projected, _inputs, lower⟩ := SourcePruningEnumerationSharedEagerChildren.prepared_child_lt
                caller.checked.native.machine.heap parentEntry rows depth free edge selected scs before middle
                symbol staged residual prepared child bucket member
              exact dite_eq_left lower

end ActualPreparedGuard

section ActualHeightResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_child_height_complete_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver := by
  induction height with
  | zero => exact eager_child_height_zero_complete_with_outputs outputOK checkEmpty edgesOf captured limit own formulas solver
  | succ height ih =>
      intro inventory caller memos metadata before seed bound ceiling bucket incoming uv continuation admitted done stopped
        packet fits known available kept closed bounded pending mass bucketBound ranked shapes selectionMembers selectionLength
        reserved growth consumers
      by_cases ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = true
      · cases incoming with
        | empty => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
        | reference name => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
        | union entry members depth free => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
        | mu entry body depth payload => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
        | node entry rows depth free =>
            let first := fallbackPlan bound ceiling continuation seed
            have initial := fallbackPlan_ge bound ceiling continuation growth seed
            have firstFits : Fits first.2 caller.checked := fits.mono initial.1
            have firstKnown : Heap (fun guard => guard ∈ first.1) caller.checked.native.machine.heap := by
              intro key edge found
              exact initial.2 (known key edge found)
            have alternativesLength : (edgesOf (.node entry rows depth free)).length ≤ limit :=
              Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
            have rowsComplete := eager_rows_complete_of_child_with_outputs outputOK (Typing := Typing) (bits := bits)
              checkEmpty edgesOf captured limit own height formulas solver ih limit
            obtain ⟨fuel, outcome, running, resources⟩ := rowsComplete inventory caller memos metadata before first
              bound ceiling bucket uv continuation admitted done stopped packet firstFits firstKnown kept mass bucketBound
              entry rows depth free available closed ranked bounded pending (edgesOf (.node entry rows depth free))
              alternativesLength (selectionMembers entry rows depth free) shapes selectionMembers selectionLength reserved.2 growth consumers
            refine ⟨fuel, outcome, ?_, resources⟩
            intro extra
            let work := fuel + extra
            let full : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold :=
              fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
                (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
                (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
                bucket edge reached cached saved
            let guarded : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold :=
              fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
                (fun inherited child current cache memos yes no =>
                  if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node entry rows depth free) then
                    SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf
                      inherited child current cache memos yes no
                  else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty work work work work work
                    inherited child current cache memos yes no)
                (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
                bucket edge reached cached saved
            have same : SourcePruningEnumerationSharedBranching.scan guarded before
                (edgesOf (.node entry rows depth free)) caller memos.query =
                SourcePruningEnumerationSharedBranching.scan full before
                  (edgesOf (.node entry rows depth free)) caller memos.query := by
              apply scan_members_congr
              intro edge member reached saved
              exact selected_guarded_eq checkEmpty work work work work work edgesOf entry rows depth free
                edge (selectionMembers entry rows depth free edge member) bucket reached before saved
                (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
            have sourceRun := SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary checkEmpty
              work work work work work edgesOf bucket (.node entry rows depth free) caller before memos.query
              (done work) (stopped work) ordinary
            exact sourceRun.trans (same.trans (running extra))
      · have fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false := by
          cases classified : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming with
          | false => rfl
          | true => exact (ordinary classified).elim
        obtain ⟨fuel, outcome, running, resources⟩ := eager_fallback_resources_with_outputs outputOK seed bound ceiling continuation admitted
          formulas solver inventory caller memos metadata before checkEmpty edgesOf bucket incoming uv done stopped packet
          bounded pending (kept.available incoming available) closed fits known mass bucketBound
          (nodeReserved_fallback bits limit own (height + 1) bound ceiling continuation admitted seed reserved) fallback
          (fun fragment reached saved after data fitted supported afterMass accepted =>
            consumers.1 fragment reached saved after data (advance seed (bound + 1)) (ceiling + bound)
              fitted supported afterMass accepted)
          (fun reached saved after outer waiting next final post query fitted supported accepted =>
            consumers.2 reached saved after outer waiting next final post query (advance seed (bound + 1)) (ceiling + bound)
              fitted supported accepted)
        have included := fallbackPlan_le_nodePlan limit own (height + 1) bound ceiling continuation growth seed
        exact ⟨fuel, outcome, running, resources_outputs_mono included.1 included.2 resources⟩

private theorem eager_child_height_complete
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver := by
  simpa only [EagerChildCompleteWithOutputs, EagerChildComplete, ChildConsumersWithOutputs, ChildConsumers, resources_outputs_true_iff] using
    (eager_child_height_complete_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver)
end ActualHeightResources

section ActualFinalizeChildInputs
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem finalize_child_inputs_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing) (before middle : Cached)
    (uv handle : Nat) (scs : List Suspended) (fragment : Fragment) (saved : Queries)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (data : ChildInputs formulas solver original metadata before scs fragment reached saved middle) :
    ∃ (next : Inventory) (final : Memos) (fuel : Nat) (after : Cached),
      Post formulas solver next original reached final ∧ final.query = saved ∧
      (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        (fuel + extra) uv fragment middle = some after) ∧
      Packet formulas solver next reached final metadata after ∧
      FragmentBound after.core.counter fragment ∧
      after.core = {middle.core with values := middle.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ∧
      after.core.values[uv]? = some (.enumerated fragment) ∧ IsRoot after.core.representatives uv
    := by
  obtain ⟨next, final, post, querySame, middlePacket, _growth, _origin,
    protects, references, fragmentBound, fragmentPending, fragmentAvoid⟩ := data
  have avoids := ready.avoids handle scs stored
  have frame := protects uv ready.inside ready.root avoids
  have middleStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
    frame.value.trans stored
  have separate := fragmentAvoid uv ready.inside ready.root avoids
  have incomingAtMiddle : EnumerationReferences.IncomingAvoid uv middle.core := by
    have allowed := references
      (fun slot => ¬UnionFind.SameClass before.core.representatives uv slot)
      incoming avoids (EnumerationReferences.fresh_separate before.core ready.safe uv ready.inside)
    intro value member sc listed related
    exact allowed value member sc listed ((frame.classes sc.var).mp related)
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := middlePacket.valid
  obtain ⟨fuel, after, finishRun, _raw, core, afterStored, _afterFlag, _afterWaiting,
    afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish⟩ :=
    SourcePruningEnumerationFinalize.complete reached.checked.native.machine.heap middle uv fragment
      (.unenumerated (some handle) scs) middleStored roots paths counts flags storage fragmentBound realized
  have afterSafe := safeFinish middlePacket.safe frame.root
  have afterPending : EnumerationReferences.PendingReferences after.core := by
    have written := EnumerationReferences.setValue_pending uv fragment middle.core
      {middle.core with values := middle.core.values.set uv (.enumerated fragment)}
      middlePacket.pending incomingAtMiddle ((EnumerationDriver.modify_success _ _ _).mpr rfl)
    rw [core]
    exact written
  have afterPacket : Packet formulas solver next reached final metadata after := by
    refine ⟨middlePacket.context, afterSafe, afterPending,
      ⟨roots, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags⟩, ?_, ?_⟩
    · obtain ⟨level, frontier, ordered⟩ := middlePacket.ordered
      obtain ⟨nextLevel, writtenOrder⟩ := EnumerationOrder.write_stratified middle.core middlePacket.safe
        level frontier uv ordered (some handle) scs middleStored fragment fragmentPending separate
      refine ⟨nextLevel, frontier + 1, ?_⟩
      rw [core]
      exact EnumerationOrder.stratified_ancestry _ [] nextLevel (frontier + 1) writtenOrder
    · rw [core]
      exact middlePacket.bounded
  have mass := (SourcePruningEnumerationFinalize.run_scalars reached.checked.native.machine.heap
    (fuel + 0) uv fragment middle after (finishRun 0)).2
  refine ⟨next, final, fuel, after, post, querySame, finishRun, afterPacket, ?_, core, mass, afterStored, ?_⟩
  · rw [core]
    exact fragmentBound
  · rw [core]
    exact frame.root

end ActualFinalizeChildInputs

section ActualCapturedResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Captured children retain the same narrowing operation in their recursive callback. -/
private theorem eager_captured_resources_with_narrow
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeWithNarrowComplete (bits := bits) narrow graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            narrow graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome) := by
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      narrow graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
    OutcomeResources formulas solver caller
      (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
    limit (bound + own) ceiling continuation growth seed
  have planFits := fits.mono planGrowth.1
  have planKnown : Heap
      (fun guard => guard ∈ (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed).1)
      caller.checked.native.machine.heap := by
    intro key edge found
    exact planGrowth.2 (known key edge found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        let outcome : Fold := .stopped [] [] (.edge (some .unhandled) (caller, memos.query))
        refine ⟨0, outcome, ?_, ?_⟩
        · intro extra
          rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
          simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
            SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
          rfl
        · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, .inr rfl, ?_⟩
          intro output member
          cases member
    | some fields =>
        rcases fields with ⟨tries, residual⟩
        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, lower, reducing⟩ :=
          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
        obtain ⟨_prepared, _middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, middleProtects⟩ := ownReceipt
        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
        have edgeBounds := (shapes parentEntry rows depth free available).2 edge selected
        have triesBound := edgeBounds.2 tries residual projected
        have inputLength : inputs.length ≤ limit := by
          simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using edgeBounds.1
        have inputFacts : ∀ value bucket, (value, bucket) ∈ inputs →
            Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
              bucket.length ≤ bound + own ∧ (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value bucket member
          obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine value bucket member
          have childRank := lower value bucket member
          obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
          cases same
          have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
          have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
            (suspendedVars before.core.counter tries)
          rw [SourcePruningEnumerationCostBounds.suspended_length] at added
          refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
            ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, by omega, ?_, childBounded, childPending⟩
          simp only [List.length_append]
          omega
        have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling := by
          rw [middleMass]
          exact mass
        let yes : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
          fun work fragments reached saved after =>
            let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
            let middle := SelectedEdge.finish residual fragment after
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.complete fragment reached saved finished))
            | none => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.finalizeStopped fragment reached saved middle))
        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
          fun work completed observation candidate =>
            SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
              (some (.stopped completed observation candidate))
        have tupleConsumers : TupleConsumers formulas solver caller metadata middle inputs uv continuation admitted yes no := by
          constructor
          · intro fragments reached saved after history current retained fitted supported afterMass accepted
            let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
            let childAfter := SelectedEdge.finish residual fragment after
            have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
              middleCore middleCounter middleProtects fragments reached saved after history
            obtain ⟨next, final, finalFuel, finished, _post, querySame, finalAt, finishedPacket,
              fragmentBound, _core, finalMass, _stored, _root⟩ :=
              finalize_child_inputs_packet formulas solver caller reached metadata before childAfter uv handle scs
                fragment saved ready stored incoming data
            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass afterMass
            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
              callback_eager_induction_resources_with_narrow narrow formulas solver next graph templates metadata uv
                fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current retained
                finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
            rw [querySame] at hookAt
            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
            let outcome : Fold := match hookOutcome with
              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
            · intro extra
              have finalizeAt := finalAt (hookFuel + extra)
              rw [← Nat.add_assoc] at finalizeAt
              have continued := hookAt (finalFuel + extra)
              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
              rw [same] at continued
              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
                (finalFuel + hookFuel + extra) uv fragment childAfter with
                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.complete fragment reached saved finished))
                | none => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
              rw [finalizeAt]
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
                simpa only [hook] using continued
              rw [hookStep]
              cases hookOutcome <;> rfl
            · cases hookOutcome <;> exact resources
          · intro completed reached saved after outer waiting next final post query current retained fitted supported _accepted
            let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
              ((.ok (some []), reached, saved, outer, waiting)) (some after)
            let outcome : Fold := .complete [receipt] [] reached saved
            have resources : OutcomeResources formulas solver reached current (finish uv outcome) := by
              refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
              intro output member
              cases member
            have enlarged := growth retained current
            exact ⟨0, outcome, fun _ => rfl, resources.mono enlarged.1 enlarged.2⟩
        have child := eager_child_height_complete (Typing := Typing) (bits := bits)
          checkEmpty edgesOf captured limit own height formulas solver
        have tuple := eager_tuple_complete_of_child (Typing := Typing) (bits := bits)
          checkEmpty edgesOf captured limit own height formulas solver child limit
        obtain ⟨fuel, outcome, running, resources⟩ := tuple inventory caller memos metadata middle seed
          (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
          inputFacts shapes selectionMembers selectionLength reserved growth tupleConsumers
        refine ⟨fuel, outcome, ?_, resources⟩
        intro extra
        rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts, reducing]
        exact running extra
  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
    refine ⟨0, outcome, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
        SourcePruningEnumerationCachedOwn.prepare, allowed]
      rfl
    · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
      intro output member
      cases member

variable {Key : Type}

private theorem eager_captured_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome) := by
  exact eager_captured_resources_with_narrow (bits := bits)
    (SourcePruningOuterNarrow.narrow holeKey keyMatches admits)
    graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
    captured limit own height inventory caller memos metadata before seed bound ceiling scs uv handle
    packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free
    available closed ranked edge selected bounded pending shapes selectionMembers selectionLength reserved

end ActualCapturedResources

section ActualCapturedRowsResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)

/-- Captured rows retain the same narrowing operation in their recursive callback. -/
private theorem eager_captured_rows_resources_with_narrow
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeWithNarrowComplete (bits := bits) narrow graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat) :
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
    Packet formulas solver inventory caller memos metadata before →
    EnumerationDriver.Ready uv before.core →
    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv before.core →
    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained)
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              narrow graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
            graph templates stop order (fuel + extra) metadata uv)
          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
 := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet _ready _stored _incoming fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending
        alternatives length _selected _shapes _selectionMembers _selectionLength _reserved
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending
        alternatives length selected shapes selectionMembers selectionLength reserved
      let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
      let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
      have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
          current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      cases alternatives with
      | nil =>
          have enlarged := iterate_ge row rowGrowth seed (count + 1)
          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
              caller.checked.native.machine.heap := by
            intro key edge found
            exact enlarged.2 (known key edge found)
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
            supported, rfl, rfl, fun _ member => by cases member⟩
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_captured_resources_with_narrow
            narrow graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
            captured limit own height inventory caller memos metadata before seed bound ceiling scs uv handle
            packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked
            edge (selected edge (by simp)) bounded pending shapes selectionMembers selectionLength firstReserved
          have farther := iterate_ge row rowGrowth (row seed) count
          cases headOutcome with
          | stopped processed outputs current =>
              refine ⟨headFuel, .stopped processed outputs current, ?_, headResources.mono farther.1 farther.2⟩
              intro extra
              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
          | complete processed outputs reached saved =>
              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, outputResources⟩ :=
                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources
              have laterReserved : ∀ index, index < count →
                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
                intro index inside
                exact reserved (index + 1) (by omega)
              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
                bound ceiling scs uv handle reachedPacket ready stored incoming reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved
              let result : Fold := match tailOutcome with
                | .complete later remaining finalCaller finalQueries =>
                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
              · intro extra
                have headAt := headRunning (tailFuel + extra)
                have tailAt := tailRunning (headFuel + extra)
                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
                rw [hs] at headAt
                rw [ts, query] at tailAt
                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
                dsimp only
                rw [tailAt]
                cases tailOutcome <;> rfl
              · obtain ⟨lastCaller, lastInventory, lastMemos, lastPost, lastFits, lastKnown, shape⟩ := tailResources
                refine ⟨lastCaller, lastInventory, lastMemos, post.trans lastPost, lastFits, lastKnown, ?_⟩
                cases tailOutcome with
                | complete later remaining finalCaller finalQueries =>
                    obtain ⟨sameCaller, sameQueries, retained⟩ := shape
                    refine ⟨sameCaller, sameQueries, ?_⟩
                    intro output member
                    rcases List.mem_append.mp member with old | fresh
                    · exact (outputResources output old).mono farther.1 farther.2
                    · exact (retained output fresh).post post
                | stopped later remaining current =>
                    obtain ⟨sameEndpoint, retained⟩ := shape
                    refine ⟨sameEndpoint, ?_⟩
                    intro output member
                    rcases List.mem_append.mp member with old | fresh
                    · exact (outputResources output old).mono farther.1 farther.2
                    · exact (retained output fresh).post post

variable {Key : Type}

private theorem eager_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat) :
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
    Packet formulas solver inventory caller memos metadata before →
    EnumerationDriver.Ready uv before.core →
    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv before.core →
    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained)
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
            graph templates stop order (fuel + extra) metadata uv)
          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
 := by
  exact eager_captured_rows_resources_with_narrow (bits := bits)
    (SourcePruningOuterNarrow.narrow holeKey keyMatches admits)
    graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
    captured limit own height count

end ActualCapturedRowsResources

section ActualOpaqueResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Opaque completion retains the same narrowing operation in its recursive callback. -/
private theorem eager_opaque_resources_with_narrow
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeWithNarrowComplete (bits := bits) narrow graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            narrow graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
  have cost : scs.length + 1 ≤ bound + 1 := by omega
  obtain ⟨headFuel, receipt, reached, saved, final, next, headRun, headPost, headQuery,
    _advanced, admitted, _pending, _history, headFits, headKnown, shape, _finalization⟩ :=
    SourcePruningEnumerationSharedSelectedOpaqueDispatch.opaque_complete_resources seed formulas solver inventory
      caller memos metadata before checkEmpty uv handle scs value packet ready stored incoming available closed
      dispatch fits (reserved.1.prefix cost) known
  have padding : Le (advance seed (scs.length + 1)).2 (advance seed (bound + 1)).2 ∧
      (advance seed (scs.length + 1)).1 ⊆ (advance seed (bound + 1)).1 :=
    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed cost,
      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed cost⟩
  have paddedFits := headFits.mono padding.1
  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
      reached.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
  subst saved
  rcases shape with completed | stopped | rejected
  · obtain ⟨fragment, after, rfl, afterPacket, _counter, afterMass⟩ := completed
    have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound := by omega
    obtain ⟨callbackFuel, continued, callbackRun, resources⟩ :=
      callback_eager_induction_resources_with_narrow narrow formulas solver next graph templates metadata uv
        fragment reached final after checkEmpty edgesOf stop order recursiveDepth recursive
        (advance seed (bound + 1)) (ceiling + bound) afterPacket admitted.2.2.1 paddedFits paddedKnown
        selectionMembers selectionLength actualMass reserved.2
    let folded : Fold := match continued with
      | .complete outputs actual queries =>
          .complete [.complete fragment reached final.query after] outputs actual queries
      | .stopped outputs reason endpoint =>
          .stopped [] outputs (.continuation (.complete fragment reached final.query after) reason endpoint)
    have fullResources := resources.post headPost
    have finished : OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed)
        (finish uv folded) := by
      cases continued <;>
        simpa only [folded, finish, SourcePruningEnumerationSharedPreparedRecursive.endpoint,
          OutcomeResources, fallbackPlan] using fullResources
    refine ⟨headFuel + callbackFuel, .complete fragment reached final.query after, folded, ?_, ?_, finished⟩
    · intro extra
      have actual := headRun (callbackFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callbackRun (headFuel + extra)
      have common : callbackFuel + (headFuel + extra) = headFuel + callbackFuel + extra := by omega
      rw [common] at actual
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual]
      cases continued <;> rfl
  · obtain ⟨after, outer, waiting, rfl, _counter, _mass⟩ := stopped
    have resources : OutcomeResources (Typing := Typing) formulas solver caller (advance seed (bound + 1))
        (.complete [] reached final.query) := by
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    refine ⟨headFuel, .stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after),
      .complete [.stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after)] [] reached final.query,
      headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · simpa only [finish, fallbackPlan] using resources.mono growth.1 growth.2
  · subst receipt
    have resources : OutcomeResources (Typing := Typing) formulas solver caller (advance seed (bound + 1))
        (.complete [] reached final.query) := by
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    have endpoints : (caller, memos.query) = (reached, final.query) := by
      exact Option.some.inj _advanced
    obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
    refine ⟨headFuel, .rejected caller memos.query before,
      .complete [.rejected caller memos.query before] [] caller memos.query, headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · have fullResources := resources.mono growth.1 growth.2
      simpa only [finish, fallbackPlan, callerSame, querySame] using fullResources

variable {Key : Type}

private theorem eager_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
  exact eager_opaque_resources_with_narrow (bits := bits)
    (SourcePruningOuterNarrow.narrow holeKey keyMatches admits)
    graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
    inventory caller memos metadata before seed bound ceiling uv handle scs value
    packet ready stored incoming available closed dispatch fits known mass bucketBound
    selectionMembers selectionLength reserved

end ActualOpaqueResources

section ActualPreparedResources
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate)

/-- Preparation retains the same narrowing operation in both recursive branches. -/
private theorem eager_prepared_resources_with_narrow
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeWithNarrowComplete (bits := bits) narrow graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ ceiling)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling) :
    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            narrow graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      narrow graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel observed outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
    OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  obtain ⟨preparationFuel, decoded, value, heap, entered, retained,
    preparedFits, _valueMass, preparedKnown, frame, enteredIncoming, sameMass⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_current
      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 fits incoming
      (fun guard => guard ∈ seed.1) known
  obtain ⟨preparationRun, _decodedLookup, preparationPost, enteredPacket, _stable, enteredReady,
    enteredStored, _counter, _values, _flags, _waiting, available, closed, _meaning, _satisfaction⟩ := retained
  let preparedCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
  have currentFits : Fits start.2 preparedCaller.checked := preparedFits
  have currentKnown : Heap (fun guard => guard ∈ start.1) preparedCaller.checked.native.machine.heap := preparedKnown
  have currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core ≤ ceiling := by
    rw [sameMass]
    exact mass
  by_cases ordinary : ∃ entry rows depth free,
      value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
  · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
    subst value
    let captured := preparedCaller.checked.native.machine.heap
    obtain ⟨heights, shapes⟩ := SourcePruningEnumerationSharedEagerCapturedBounds.captured_payload_bounds
      start captured enteredPacket.context.ready.semantic.ready.semantic.1.normal.facts.linked
      (SourceCurrentConstrainedCapRequiredResources.of_checked currentFits) currentKnown
    have nodeHeight := heights (.node entry rows depth free) available
    have positive : 0 < limit := by
      change MergedOrdinaryHeight.edgesHeight rows + 1 ≤ limit at nodeHeight
      omega
    let height := limit - 1
    have heightSame : height + 1 = limit := by dsimp only [height]; omega
    have ranked : MergedOrdinaryHeight.height (.node entry rows depth free) ≤ height + 1 := by
      rw [heightSame]
      exact nodeHeight
    have computed : nodeReserved bits limit own (height + 1) ceiling ceiling continuation admitted start := by
      rw [heightSame]
      exact planned
    unfold nodeReserved at computed
    let first := fallbackPlan ceiling ceiling continuation start
    let row := fun current => tuplePlan (nodePlan limit own height) limit (ceiling + own) ceiling continuation current
    have firstGrowth := fallbackPlan_ge ceiling ceiling continuation growth start
    have firstKnown : Heap (fun guard => guard ∈ first.1) preparedCaller.checked.native.machine.heap := by
      intro key edge found
      exact firstGrowth.2 (currentKnown key edge found)
    have rowReserved : ∀ index, index < limit →
        tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
          limit (ceiling + own) ceiling continuation admitted (iterate row first index) := computed.2
    have length : (edgesOf (.node entry rows depth free)).length ≤ limit :=
      Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
    have bounded : ∀ sc ∈ scs, sc.var < entered.core.counter :=
      enteredReady.safe.1.values _ (List.mem_of_getElem? enteredStored)
    have pending := EnumerationReferences.pending_inputs entered.core enteredPacket.pending uv (some handle) scs enteredStored
    obtain ⟨branchFuel, outcome, branchRun, certificate⟩ := eager_captured_rows_resources_with_narrow
      narrow graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      captured limit own height limit inventory preparedCaller memos metadata entered first ceiling ceiling scs uv handle
      enteredPacket enteredReady enteredStored enteredIncoming (currentFits.mono firstGrowth.1) firstKnown
      (SourceEqualityRequiredCache.pure_keeps captured enteredPacket.context.ready.semantic.ready)
      currentMass bucketBound entry rows depth free available closed ranked bounded pending
      (edgesOf (.node entry rows depth free)) length (selectionMembers entry rows depth free) shapes
      selectionMembers selectionLength rowReserved
    have finalSame : eagerFinal (recursiveDepth + 1) seed ceiling = iterate row first limit := by
      change nodePlan limit own limit ceiling ceiling continuation start = _
      calc
        nodePlan limit own limit ceiling ceiling continuation start =
            nodePlan limit own (height + 1) ceiling ceiling continuation start :=
          congrArg (fun h => nodePlan limit own h ceiling ceiling continuation start) heightSame.symm
        _ = iterate row first limit := by
          unfold nodePlan
          rfl
    have resources : OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling)
        (finish uv outcome) := by
      rw [finalSame]
      exact certificate.post preparationPost
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done (.node entry rows depth free) heap)),
      outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have atBranch := branchRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at atBranch
    unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
    rw [atPreparation]
    simp only [nonterminal, Bool.false_eq_true, ↓reduceIte]
    rw [frame, atBranch]
  · have dispatch : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false := by
      cases value with
      | node entry rows depth free =>
          cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
          | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
          | true => rfl
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ => rfl
    obtain ⟨branchFuel, receipt, outcome, rawRun, receiptRun, certificate⟩ := eager_opaque_resources_with_narrow
      narrow graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      inventory preparedCaller memos metadata entered start ceiling ceiling uv handle scs value enteredPacket enteredReady
      enteredStored enteredIncoming available closed dispatch currentFits currentKnown currentMass bucketBound
      selectionMembers selectionLength (nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned)
    have enlarged := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
    have resources : OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling)
        (finish uv outcome) := (certificate.mono enlarged.1 enlarged.2).post preparationPost
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)), outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have rawAt := rawRun (preparationFuel + extra)
    have continued := receiptRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at rawAt continued
    have composed : SourcePruningEnumerationSharedReceiptContinuation.run
        (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query) = outcome := by
      rw [rawAt]
      exact continued
    have actual : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) edgesOf)
        (hook (preparationFuel + branchFuel + extra)) checkEmpty
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) uv edgesOf caller before memos.query =
      (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)),
        some (SourcePruningEnumerationSharedReceiptContinuation.run
          (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
          (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query))) := by
      unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      rw [atPreparation]
      cases value with
      | node entry rows depth free =>
          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, here⟩).elim
            | true => rfl
          simp only [terminal, ↓reduceIte, frame, preparedCaller]
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
            simp only [here, Bool.false_eq_true, ↓reduceIte, frame, preparedCaller]
    rw [composed] at actual
    exact actual

variable {Key : Type}

private theorem eager_prepared_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ ceiling)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling) :
    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) := by
  exact eager_prepared_resources_with_narrow (bits := bits)
    (SourcePruningOuterNarrow.narrow holeKey keyMatches admits)
    graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
    inventory caller memos metadata before seed ceiling uv handle scs
    packet ready stored incoming fits known mass bucketBound selectionMembers selectionLength reserved

end ActualPreparedResources

section ActualEagerExpansion
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationSelectedStep (runPrefix)
open SourcePruningEnumerationSharedRecursive (checkpoint_resources CurrentPrefixFacts)
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound

private theorem eager_expansion_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  have firstReserved := nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned
  have finalGrowth := eagerFinal_ge (recursiveDepth + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
  have stageGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
  obtain ⟨currentFuel, phases⟩ := checkpoint_resources holeKey keyMatches admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  obtain ⟨legacyFuel, legacyComplete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet
  let prefixFuel := currentFuel + legacyFuel
  have shift (extra : Nat) : currentFuel + (legacyFuel + extra) = prefixFuel + extra := by
    dsimp only [prefixFuel]
    omega
  have legacy (extra : Nat) : SourcePruningEnumerationSelectedStep.PrefixValid
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + extra) uv caller before memos
      (runPrefix holeKey keyMatches admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query) := by
    have valid := legacyComplete (currentFuel + extra) uv chosen
    have common : legacyFuel + (currentFuel + extra) = prefixFuel + extra := by
      dsimp only [prefixFuel]
      omega
    simpa only [common] using valid
  rcases phases with ⟨checked, originalPhase⟩ | ⟨checked, heap, originalPhase⟩ |
    ⟨checked, phaseValue, heap, after, _nonempty, originalPhase⟩
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have valid := legacy 0
    rw [(phase 0).1] at valid
    have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet _ valid (phase 0).1
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
    · have certificate : OutcomeResources (Typing := Typing) formulas solver caller seed
          (.complete [] caller memos.query) := by
        refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_, certificate.mono finalGrowth.1 finalGrowth.2⟩
      intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, observed]
    · let parkedSeed := advance start (ceiling + 1)
      let parkedMass := ceiling + ceiling
      have headGrowth : Le start.2 parkedSeed.2 ∧ start.1 ⊆ parkedSeed.1 :=
        ⟨SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge start (ceiling + 1),
          SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge start (ceiling + 1)⟩
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : mass checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound firstReserved.2
      have included := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
      have callbackResources : OutcomeResources formulas solver caller
          (fallbackPlan ceiling ceiling continuation start) outcome := resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, callbackResources.mono included.1 included.2⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, observed]
      dsimp only
      rw [framed]
      exact actual
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
    have certificate : OutcomeResources (Typing := Typing) formulas solver caller start
        (.complete [] reached memos.query) := by
      refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
        current.2.2, rfl, query.symm, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, (phase extra).1]
    · exact certificate.mono stageGrowth.1 stageGrowth.2
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨_action, prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      CurrentPrefixFacts.right_packet current.1
    have valid := legacy 0
    rw [prefixAt] at valid
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ valid
    obtain ⟨handle, scs, _value, _oldMemos, _oldPost, _oldQuery, _oldPacket, ready, stored,
      _decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      _oldFits, _oldKnown⟩ := admission
    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
        reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : mass after.core ≤ ceiling := Nat.le_trans
      (SourcePruningEnumerationPrefixMass.retained_le holeKey keyMatches admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt)
      initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    obtain ⟨scanFuel, _observation, result, scanRun, certificate⟩ := eager_prepared_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      inventory reached middleMemos metadata after seed ceiling uv handle scs middlePacket ready stored incoming
      middleFits middleKnown currentMass inheritedLength selectionMembers selectionLength reserved
    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost⟩
    intro extra
    obtain ⟨currentAction, currentPrefix, _current⟩ := phase (scanFuel + extra)
    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [common] at currentPrefix
    have actual := scanRun (prefixFuel + extra)
    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [scanCommon, middleQuery] at actual
    rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
      ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, currentPrefix]
    dsimp only
    dsimp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] at actual
    rw [actual]

end ActualEagerExpansion

section ActualIdentityEagerExpansion
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationSharedRecursive (CurrentPrefixFacts)
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound

/-- The actual identity checkpoint supplies every phase of one eager expansion. -/
private theorem identity_eager_expansion_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeWithNarrowComplete (Typing := Unit) (bits := bits)
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Unit)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before = some (.expand uv)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  have firstReserved := nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned
  have finalGrowth := eagerFinal_ge (recursiveDepth + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
  have stageGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
  obtain ⟨prefixFuel, phases⟩ := SourcePruningEnumerationSharedRecursive.identity_checkpoint_resources
    graph checkEmpty edgesOf metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  rcases phases with ⟨checked, checkedMass, phase⟩ | ⟨checked, phase⟩ |
    ⟨handle, scs, value, after, _nonempty, _encoded, ready, stored, incoming, lengths, sameMass, phase⟩
  · have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata checked = some .stuck
    · have certificate : OutcomeResources (Typing := Unit) formulas solver caller seed
          (.complete [] caller memos.query) := by
        refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_, certificate.mono finalGrowth.1 finalGrowth.2⟩
      intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, observed]
    · let parkedSeed := advance start (ceiling + 1)
      let parkedMass := ceiling + ceiling
      have headGrowth : Le start.2 parkedSeed.2 ∧ start.1 ⊆ parkedSeed.1 :=
        ⟨SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge start (ceiling + 1),
          SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge start (ceiling + 1)⟩
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : mass checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound firstReserved.2
      have included := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
      have callbackResources : OutcomeResources formulas solver caller
          (fallbackPlan ceiling ceiling continuation start) outcome := resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, callbackResources.mono included.1 included.2⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, observed]
      dsimp only
      rw [framed]
      exact actual
  · let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
        ⟨caller.checked.native.machine.heap, caller.checked.operations⟩) caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
    have certificate : OutcomeResources (Typing := Unit) formulas solver caller start
        (.complete [] reached memos.query) := by
      refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
        current.2.2, rfl, query.symm, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, (phase extra).1]
    · exact certificate.mono stageGrowth.1 stageGrowth.2
  · let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
        ⟨caller.checked.native.machine.heap, caller.checked.operations⟩) caller.fourth caller.merge
    obtain ⟨prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      CurrentPrefixFacts.right_packet current.1
    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
        reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : mass after.core ≤ ceiling := by
      rw [sameMass]
      exact initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    obtain ⟨scanFuel, _observation, result, scanRun, certificate⟩ := eager_prepared_resources_with_narrow
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf none (fun _ _ => none)
      formulas solver recursiveDepth recursive inventory reached middleMemos metadata after seed ceiling uv handle scs
      middlePacket ready stored incoming middleFits middleKnown currentMass inheritedLength
      selectionMembers selectionLength reserved
    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost⟩
    intro extra
    have currentPrefix := (phase (scanFuel + extra)).1
    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [common] at currentPrefix
    have actual := scanRun (prefixFuel + extra)
    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [scanCommon, middleQuery] at actual
    rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, currentPrefix]
    dsimp only
    rw [actual]

end ActualIdentityEagerExpansion

section ActualIdentityEagerDepthClosure
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual identity decision retains its literal zero-depth output resources. -/
private theorem identity_resume_eager_zero_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Unit) (decision : Option Next) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ outcome,
      (∀ workFuel, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) workFuel 0 metadata caller memos.query before decision = outcome) ∧
      OutcomeResources formulas solver caller seed outcome := by
  cases decision with
  | none =>
      refine ⟨.complete [⟨some metadata, before, caller, memos.query⟩] caller memos.query,
        (fun _ => rfl), caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨inventory, memos, metadata, Post.refl packet.context, rfl, packet, Or.inr rfl, bounded, known⟩
  | some selected =>
      cases selected with
      | done =>
          refine ⟨.complete [⟨none, before, caller, memos.query⟩] caller memos.query,
            (fun _ => rfl), caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          have same := List.mem_singleton.mp member
          subst output
          exact ⟨inventory, memos, metadata, Post.refl packet.context, rfl, packet, Or.inl rfl, bounded, known⟩
      | stuck =>
          refine ⟨.complete [] caller memos.query, (fun _ => rfl),
            caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim
      | expand uv =>
          refine ⟨.stopped [] (.exhausted uv metadata before) (some (caller, memos.query)),
            (fun _ => rfl), caller, inventory, memos, Post.refl packet.context,
            bounded, known, Or.inr rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim

/-- The actual identity worker retains its resources at every finite recursive depth. -/
private theorem identity_eager_resume_complete
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) :
    EagerResumeWithNarrowComplete (Typing := Unit) (bits := bits)
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) formulas solver recursiveDepth := by
  induction recursiveDepth with
  | zero =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        _selectionMembers _selectionLength _initialMass _reserved
      obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
        graph checkEmpty edgesOf formulas solver inventory caller memos before metadata
        (SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before)
        seed packet bounded known
      exact ⟨0, outcome, fun extra => running (0 + extra), resources⟩
  | succ depth ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved
      have growth := eagerFinal_ge (depth + 1) seed ceiling
      cases decision : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before with
      | none =>
          obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
            graph checkEmpty edgesOf formulas solver inventory caller memos before metadata none seed packet bounded known
          refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
          intro extra
          simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
      | some selected =>
          cases selected with
          | done =>
              obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
                graph checkEmpty edgesOf formulas solver inventory caller memos before metadata (some .done)
                seed packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | stuck =>
              obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
                graph checkEmpty edgesOf formulas solver inventory caller memos before metadata (some .stuck)
                seed packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | expand uv =>
              exact identity_eager_expansion_resources graph checkEmpty edgesOf formulas solver depth ih
                inventory caller memos before metadata uv seed ceiling packet bounded known
                selectionMembers selectionLength initialMass reserved decision

/-- Original reservations give one stable actual identity outcome and every output resource. -/
theorem runEager_identity_finite_complete_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Unit)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome := by
  have complete := identity_eager_resume_complete (bits := bits)
    graph checkEmpty edgesOf formulas solver recursiveFuel
  obtain ⟨fuel, outcome, running, resources⟩ := complete inventory caller memos before metadata seed ceiling
    packet bounded known selectionMembers selectionLength initialMass reserved
  exact ⟨fuel, outcome, fun extra => running extra, resources⟩

end ActualIdentityEagerDepthClosure

section ActualEagerDepthClosure
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_resume_complete
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) :
    EagerResumeComplete (Typing := Typing) (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth := by
  induction recursiveDepth with
  | zero =>
      exact eager_resume_zero_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver
  | succ depth ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved
      have growth := eagerFinal_ge (depth + 1) seed ceiling
      cases decision : SourcePruningEnumerationRestart.decision stop order metadata before with
      | none =>
          obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
            checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata none seed packet bounded known
          refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
          intro extra
          simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
            SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
      | some selected =>
          cases selected with
          | done =>
              obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
                checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata (some .done) seed
                packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | stuck =>
              obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
                checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata (some .stuck) seed
                packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | expand uv =>
              exact eager_expansion_resources holeKey keyMatches admits graph templates checkEmpty edgesOf stop order
                formulas solver depth ih inventory caller memos before metadata uv seed ceiling packet bounded known
                selectionMembers selectionLength initialMass reserved decision

/-- Current reservations give one stable eager outcome and retain every output resource. -/
theorem runEager_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome  := by
  have complete := eager_resume_complete (Typing := Typing) (bits := bits) holeKey fits admits graph templates
    checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨fuel, outcome, running, resources⟩ := complete inventory caller memos before metadata seed ceiling
    packet bounded known selectionMembers selectionLength initialMass reserved
  exact ⟨fuel, outcome, fun extra => running extra, resources⟩

end ActualEagerDepthClosure

section EagerRoleData
variable [DecidableEq (EdgeKey Symbol Constraint)]

private def ProgramChildInputs
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
    (bucket : List Suspended) (fragment : Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached) : Prop :=
  ChildInputs formulas solver original metadata before bucket fragment reached saved after ∧
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal reached.checked.native.machine.heap after.core marked ∧
    SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked fragment

private def ProgramTupleInputs
    (valid : Constraint → Prop) (literal : String → Symbol) (marked programIndex : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
    (inputs : List (Node × List Suspended)) (fragments : List Fragment)
    (reached : Caller (bits + 2)) (saved : Queries) (after : Cached) : Prop :=
  TupleInputs formulas solver original metadata before inputs fragments reached saved after ∧
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal reached.checked.native.machine.heap after.core marked ∧
    fragments.length = inputs.length ∧
    ∀ index fragment, programIndex index → fragments[index]? = some fragment →
      SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked fragment

private def ProgramChildConsumersWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragment reached saved after,
    ProgramChildInputs valid literal marked formulas solver original metadata before bucket fragment reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome))

private def ProgramChildConsumers
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragment reached saved after,
    ProgramChildInputs valid literal marked formulas solver original metadata before bucket fragment reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome))

private def ProgramTupleConsumersWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked programIndex : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
    (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragments reached saved after,
    ProgramTupleInputs valid literal marked programIndex formulas solver original metadata before inputs fragments reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragments reached saved after = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (completed : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    (∀ index fragment, programIndex index → completed[index]? = some fragment →
      SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked fragment) →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) completed ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResourcesWithOutputs outputOK formulas solver reached (continuation retained current) (finish uv outcome))

private def ProgramTupleConsumers
    (valid : Constraint → Prop) (literal : String → Symbol) (marked programIndex : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
    (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
  (∀ fragments reached saved after,
    ProgramTupleInputs valid literal marked programIndex formulas solver original metadata before inputs fragments reached saved after →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragments reached saved after = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome)) ∧
  (∀ (completed : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
      (next : Inventory) (final : Memos),
    Post formulas solver next original reached final → final.query = saved →
    (∀ index fragment, programIndex index → completed[index]? = some fragment →
      SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked fragment) →
    ∀ current retained, Fits current.2 reached.checked →
      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
      ∃ fuel outcome,
        (∀ extra, stopped (fuel + extra) completed ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome))
end EagerRoleData

section EagerRoleOperations
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def EagerProgramChildCompleteWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  let literal := SourceSynthesisLabelProgramBuildRoles.literal
  ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
    ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (bucket : List Suspended) (incoming : Node) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    Available captured incoming → SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    incoming.free = [] → (∀ sc ∈ bucket, sc.var < before.core.counter) → InputsPending before.core bucket →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → bucket.length ≤ bound →
    MergedOrdinaryHeight.height incoming ≤ height →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    (∀ held, marked held → Avoids before.core.representatives held bucket) →
    SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming →
    EnumerationSemantics.ValidSuspended bucket →
    SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    nodeReserved bits limit own height bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ProgramChildConsumersWithOutputs outputOK valid literal marked formulas solver caller metadata before bucket uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller
        before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (nodePlan limit own height bound ceiling continuation seed) (finish uv outcome)

private def EagerProgramChildComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  let literal := SourceSynthesisLabelProgramBuildRoles.literal
  ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
    ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (bucket : List Suspended) (incoming : Node) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    Available captured incoming → SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    incoming.free = [] → (∀ sc ∈ bucket, sc.var < before.core.counter) → InputsPending before.core bucket →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → bucket.length ≤ bound →
    MergedOrdinaryHeight.height incoming ≤ height →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    (∀ held, marked held → Avoids before.core.representatives held bucket) →
    SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming →
    EnumerationSemantics.ValidSuspended bucket →
    SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    nodeReserved bits limit own height bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ProgramChildConsumers valid literal marked formulas solver caller metadata before bucket uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller
        before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResources formulas solver caller
        (nodePlan limit own height bound ceiling continuation seed) (finish uv outcome)


private def EagerProgramTupleCompleteWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  let literal := SourceSynthesisLabelProgramBuildRoles.literal
  ∀ (valid : Constraint → Prop) (marked programIndex : Nat → Prop),
    ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → inputs.length ≤ count →
    (∀ child bucket, (child, bucket) ∈ inputs →
      Available captured child ∧ child.free = [] ∧ MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
        (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    (∀ held, marked held → ∀ value bucket, (value, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
    (∀ index value bucket, inputs[index]? = some (value, bucket) → programIndex index →
      SourceSynthesisHereditaryProgramFields.ValueFields valid literal value ∧
        EnumerationSemantics.ValidSuspended bucket ∧
        SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ProgramTupleConsumersWithOutputs outputOK valid literal marked programIndex formulas solver caller metadata before inputs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) inputs caller before memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome)

private def EagerProgramTupleComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  let literal := SourceSynthesisLabelProgramBuildRoles.literal
  ∀ (valid : Constraint → Prop) (marked programIndex : Nat → Prop),
    ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (inputs : List (Node × List Suspended)) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → inputs.length ≤ count →
    (∀ child bucket, (child, bucket) ∈ inputs →
      Available captured child ∧ child.free = [] ∧ MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
        (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    (∀ held, marked held → ∀ value bucket, (value, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
    (∀ index value bucket, inputs[index]? = some (value, bucket) → programIndex index →
      SourceSynthesisHereditaryProgramFields.ValueFields valid literal value ∧
        EnumerationSemantics.ValidSuspended bucket ∧
        SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ProgramTupleConsumers valid literal marked programIndex formulas solver caller metadata before inputs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) inputs caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome)

end EagerRoleOperations

section EagerProgramTupleProof
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_tuple_nil_resources_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked programIndex : Nat → Prop)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (uv : Nat)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before) (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed)
    (consumers : ProgramTupleConsumersWithOutputs outputOK valid literal marked programIndex formulas solver caller metadata before []
      uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
  let visit : Nat → Visitor := fun fuel =>
    SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty fuel fuel fuel fuel fuel edgesOf
  have inputs : ProgramTupleInputs valid literal marked programIndex formulas solver caller metadata before [] []
      caller memos.query before :=
    ⟨tuple_inputs_nil formulas solver inventory caller memos metadata before packet, slots, rfl,
      by intro index fragment _wanted selected; cases selected⟩
  exact tuple_nil_reserved_resources_with_outputs outputOK limit own height count bound ceiling continuation admitted growth seed formulas solver
    caller memos before uv visit done stopped fits known mass reserved
    (fun retained current fitted supported mass accepted => consumers.1 [] caller memos.query before
      inputs current retained fitted supported mass accepted)

private theorem eager_program_tuple_nil_resources
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked programIndex : Nat → Prop)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (uv : Nat)
    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before) (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed)
    (consumers : ProgramTupleConsumers valid literal marked programIndex formulas solver caller metadata before []
      uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
  simpa only [resources_outputs_true_iff] using
    (eager_program_tuple_nil_resources_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf limit own height count bound ceiling continuation admitted growth seed formulas solver valid literal marked programIndex inventory caller memos metadata before uv done stopped packet fits known mass slots reserved
      (by simpa only [ProgramTupleConsumersWithOutputs, ProgramTupleConsumers, resources_outputs_true_iff] using consumers))

private theorem eager_program_tuple_complete_of_child_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (programChild : EagerProgramChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerProgramTupleCompleteWithOutputs outputOK (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height count formulas solver := by
  classical
  let literal : String → Symbol := SourceSynthesisLabelProgramBuildRoles.literal
  induction count with
  | zero =>
      intro valid marked programIndex inventory caller memos metadata before seed bound ceiling inputs uv
        continuation admitted done stopped packet fits known _kept mass length _genuine slots _avoids _childFields
        _shapes _selectionMembers _selectionLength reserved growth consumers
      cases inputs with
      | nil =>
          exact eager_program_tuple_nil_resources_with_outputs outputOK checkEmpty edgesOf limit own height 0 bound ceiling continuation admitted growth
            seed formulas solver valid literal marked programIndex inventory caller memos metadata before uv done stopped
            packet fits known mass slots reserved consumers
      | cons first rest => simp only [List.length_cons] at length; omega
  | succ count ih =>
      intro valid marked programIndex inventory caller memos metadata before seed bound ceiling inputs uv
        continuation admitted done stopped packet fits known kept mass length genuine slots avoids childFields
        shapes selectionMembers selectionLength reserved growth consumers
      cases inputs with
      | nil =>
          exact eager_program_tuple_nil_resources_with_outputs outputOK checkEmpty edgesOf limit own height (count + 1) bound ceiling continuation admitted growth
            seed formulas solver valid literal marked programIndex inventory caller memos metadata before uv done stopped
            packet fits known mass slots reserved consumers
      | cons input rest =>
          rcases input with ⟨incoming, bucket⟩
          obtain ⟨available, closed, ranked, bucketBound, bounded, pending⟩ := genuine incoming bucket (by simp)
          let tailPlan := fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current
          let tailAdmitted := fun retained current => tupleReserved (nodePlan limit own height)
            (nodeReserved bits limit own height) count bound retained continuation admitted current
          let yes : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
            fun fuel fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty fuel fuel fuel fuel fuel edgesOf)
              (fun fragments => done fuel (fragment :: fragments))
              (fun completed => stopped fuel (fragment :: completed)) rest reached after saved
          let no : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
            fun fuel observation candidate => stopped fuel [] observation candidate
          have tailGrowth : ∀ retained current, Le current.2 (tailPlan retained current).2 ∧
              current.1 ⊆ (tailPlan retained current).1 := by
            intro retained current
            exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
              count bound retained continuation growth current
          have success
              (fragment : Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
              (head : ChildInputs formulas solver caller metadata before bucket fragment reached saved after)
              (headSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
                reached.checked.native.machine.heap after.core marked)
              (headRole : programIndex 0 → SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked fragment)
              (current : Seed) (retained : Nat) (fitted : Fits current.2 reached.checked)
              (supported : Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap)
              (afterMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained)
              (admittedAfter : tailAdmitted retained current) :
              ∃ fuel outcome, (∀ extra, yes (fuel + extra) fragment reached saved after = outcome) ∧
                OutcomeResourcesWithOutputs outputOK formulas solver reached (tailPlan retained current) (finish uv outcome) := by
            have currentGenuine : ∀ value retainedBucket, (value, retainedBucket) ∈ (incoming, bucket) :: rest →
                Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
                (∀ sc ∈ retainedBucket, sc.var < before.core.counter) ∧ InputsPending before.core retainedBucket := by
              intro value retainedBucket member
              obtain ⟨oldAvailable, childClosed, _rank, _width, childBounded, childPending⟩ := genuine value retainedBucket member
              exact ⟨kept.available value oldAvailable, childClosed, childBounded, childPending⟩
            have combined := child_then_tuple_inputs formulas solver inventory caller memos metadata before incoming bucket rest
              packet currentGenuine fragment reached saved after head
            obtain ⟨next, final, post, query, afterPacket, _growth, _origin, protection,
              _references, _bounded, _pending, _fragmentAvoid⟩ := head
            have tailAvoids : ∀ held, marked held → ∀ value retainedBucket, (value, retainedBucket) ∈ rest →
                Avoids after.core.representatives held retainedBucket := by
              intro held tagged value retainedBucket member
              have frame := protection held (slots.bounded held tagged) (slots.roots held tagged)
                (avoids held tagged incoming bucket (by simp))
              exact frame.avoids retainedBucket (avoids held tagged value retainedBucket (List.mem_cons_of_mem _ member))
            have tailGenuine : ∀ value retainedBucket, (value, retainedBucket) ∈ rest →
                Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
                  retainedBucket.length ≤ bound ∧ (∀ sc ∈ retainedBucket, sc.var < after.core.counter) ∧
                    InputsPending after.core retainedBucket := by
              intro value retainedBucket member
              obtain ⟨oldAvailable, childClosed, childRanked, width, _bounded, _pending⟩ :=
                genuine value retainedBucket (List.mem_cons_of_mem _ member)
              obtain ⟨_available, _closed, childBounded, childPending⟩ := combined.1 value retainedBucket member
              exact ⟨oldAvailable, childClosed, childRanked, width, childBounded, childPending⟩
            let tailIndex := fun index => programIndex (index + 1)
            have tailFields : ∀ index value retainedBucket, rest[index]? = some (value, retainedBucket) → tailIndex index →
                SourceSynthesisHereditaryProgramFields.ValueFields valid literal value ∧
                  EnumerationSemantics.ValidSuspended retainedBucket ∧
                  SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion retainedBucket := by
              intro index value retainedBucket selected wanted
              exact childFields (index + 1) value retainedBucket selected wanted
            let tailDone : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
              fun fuel fragments => done fuel (fragment :: fragments)
            let tailStopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
              fun fuel completed => stopped fuel (fragment :: completed)
            have tailConsumers : ProgramTupleConsumersWithOutputs outputOK valid literal marked tailIndex formulas solver reached metadata after rest
                uv continuation admitted tailDone tailStopped := by
              constructor
              · intro fragments finalCaller queries finished history entry ceiling fitted supported mass accepted
                obtain ⟨historyData, finishedSlots, size, roles⟩ := history
                have allRoles : ∀ index child, programIndex index → (fragment :: fragments)[index]? = some child →
                    SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked child := by
                  intro index child wanted selected
                  cases index with
                  | zero =>
                      have same : fragment = child := Option.some.inj selected
                      subst child
                      exact headRole wanted
                  | succ index => exact roles index child wanted selected
                have data : ProgramTupleInputs valid literal marked programIndex formulas solver caller metadata before
                    ((incoming, bucket) :: rest) (fragment :: fragments) finalCaller queries finished :=
                  ⟨combined.2 fragments finalCaller queries finished historyData, finishedSlots, congrArg Nat.succ size, allRoles⟩
                exact consumers.1 (fragment :: fragments) finalCaller queries finished data entry ceiling fitted supported mass accepted
              · intro completed finalCaller queries finished outer waiting inventory memos later query prefixRoles
                  entry ceiling fitted supported accepted
                have allRoles : ∀ index child, programIndex index → (fragment :: completed)[index]? = some child →
                    SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked child := by
                  intro index child wanted selected
                  cases index with
                  | zero =>
                      have same : fragment = child := Option.some.inj selected
                      subst child
                      exact headRole wanted
                  | succ index => exact prefixRoles index child wanted selected
                exact consumers.2 (fragment :: completed) finalCaller queries finished outer waiting inventory memos
                  (post.trans later) query allRoles entry ceiling fitted supported accepted
            have tailLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
            obtain ⟨fuel, outcome, running, resources⟩ := ih valid marked tailIndex next reached final metadata after
              current bound retained rest uv continuation admitted tailDone tailStopped afterPacket fitted supported
              (kept.trans post.effects.keeps) afterMass tailLength tailGenuine headSlots tailAvoids tailFields shapes
              selectionMembers selectionLength admittedAfter growth tailConsumers
            refine ⟨fuel, outcome, ?_, resources⟩
            intro extra
            simpa only [yes, tailDone, tailStopped, query] using running extra
          have failure (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
              (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
              (next : Inventory) (final : Memos) (post : Post formulas solver next caller reached final)
              (query : final.query = saved) (current : Seed) (retained : Nat) (fitted : Fits current.2 reached.checked)
              (supported : Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap)
              (accepted : tailAdmitted retained current) :
              ∃ fuel outcome,
                (∀ extra, no (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
                OutcomeResourcesWithOutputs outputOK formulas solver reached (tailPlan retained current) (finish uv outcome) := by
            let entry := advance current (count * (bound + 1))
            have entryFits : Fits entry.2 reached.checked := fitted.mono
              (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge current (count * (bound + 1)))
            have entryKnown : Heap (fun guard => guard ∈ entry.1) reached.checked.native.machine.heap := by
              intro key edge found
              exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge current
                (count * (bound + 1)) (supported key edge found)
            have entryAdmitted : admitted (retained + count * bound) entry :=
              tupleReserved_first_callback bits limit own height count bound retained continuation admitted current accepted
            have noRoles : ∀ index fragment, programIndex index → ([] : List Fragment)[index]? = some fragment →
                SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked fragment := by
              intro index fragment _wanted selected
              cases selected
            obtain ⟨fuel, outcome, running, resources⟩ := consumers.2 [] reached saved after outer waiting next final
              post query noRoles entry (retained + count * bound) entryFits entryKnown entryAdmitted
            have included := first_callback_le_tuple_of_growth limit own height count bound retained continuation growth current
            exact ⟨fuel, outcome, running, resources_outputs_mono included.1 included.2 resources⟩
          by_cases demanded : programIndex 0
          · obtain ⟨fields, validTries, paths⟩ := childFields 0 incoming bucket rfl demanded
            have headConsumers : ProgramChildConsumersWithOutputs outputOK valid literal marked formulas solver caller metadata before bucket uv
                tailPlan tailAdmitted yes no := by
              constructor
              · intro fragment reached saved after head current retained fitted supported afterMass accepted
                exact success fragment reached saved after head.1 head.2.1 (fun _ => head.2.2)
                  current retained fitted supported afterMass accepted
              · exact failure
            obtain ⟨fuel, outcome, running, resources⟩ := programChild valid marked inventory caller memos metadata before
              seed bound ceiling bucket incoming uv tailPlan tailAdmitted yes no packet fits known available kept closed bounded
              pending mass bucketBound ranked slots (fun held tagged => avoids held tagged incoming bucket (by simp))
              fields validTries paths shapes selectionMembers selectionLength reserved tailGrowth headConsumers
            refine ⟨fuel, outcome, ?_, resources⟩
            intro extra
            change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller before
              memos.query (yes (fuel + extra)) (no (fuel + extra)) = outcome
            exact running extra
          · have headConsumers : ChildConsumersWithOutputs outputOK formulas solver caller metadata before bucket uv tailPlan tailAdmitted yes no := by
              constructor
              · intro fragment reached saved after head current retained fitted supported afterMass accepted
                have headSlots := child_inputs_program_slots valid literal marked formulas solver caller reached metadata before
                  after bucket fragment saved packet.safe slots (fun held tagged => avoids held tagged incoming bucket (by simp)) head
                exact success fragment reached saved after head headSlots (fun wanted => (demanded wanted).elim)
                  current retained fitted supported afterMass accepted
              · exact failure
            have child := eager_child_height_complete_with_outputs outputOK (Typing := Typing) (bits := bits)
              checkEmpty edgesOf captured limit own height formulas solver
            obtain ⟨fuel, outcome, running, resources⟩ := child inventory caller memos metadata before seed bound ceiling bucket
              incoming uv tailPlan tailAdmitted yes no packet fits known available kept closed bounded pending mass bucketBound
              ranked shapes selectionMembers selectionLength reserved tailGrowth headConsumers
            refine ⟨fuel, outcome, ?_, resources⟩
            intro extra
            change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller before
              memos.query (yes (fuel + extra)) (no (fuel + extra)) = outcome
            exact running extra

private theorem eager_program_tuple_complete_of_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (programChild : EagerProgramChildComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerProgramTupleComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height count formulas solver
    := by
  simpa only [EagerProgramTupleCompleteWithOutputs, EagerProgramTupleComplete, ProgramTupleConsumersWithOutputs, ProgramTupleConsumers, resources_outputs_true_iff] using
    (eager_program_tuple_complete_of_child_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver
      (by simpa only [EagerProgramChildCompleteWithOutputs, EagerProgramChildComplete, ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using programChild) count)

end EagerProgramTupleProof

section ActualProgramSelectedResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_selected_resources_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (programChild : EagerProgramChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
      SourceSynthesisLabelProgramBuildRoles.literal caller.checked.native.machine.heap before.core marked)
    (avoids : ∀ held, marked held → Avoids before.core.representatives held scs)
    (fields : SourceSynthesisHereditaryProgramFields.EdgeFields valid SourceSynthesisLabelProgramBuildRoles.literal edge)
    (suspendedValid : EnumerationSemantics.ValidSuspended scs)
    (annotationPaths : SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (consumers : ProgramChildConsumersWithOutputs outputOK valid SourceSynthesisLabelProgramBuildRoles.literal marked formulas solver caller metadata before scs uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitSelected
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query)
        scs edge caller before memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome) := by
  let literal : String → Symbol := SourceSynthesisLabelProgramBuildRoles.literal
  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
    limit (bound + own) ceiling continuation growth seed
  have planFits := fits.mono planGrowth.1
  have planKnown : Heap
      (fun guard => guard ∈ (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed).1)
      caller.checked.native.machine.heap := by
    intro key edge found
    exact planGrowth.2 (known key edge found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        let outcome : Fold := .stopped [] [] (.edge (some .unhandled) (caller, memos.query))
        refine ⟨0, outcome, ?_, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
            SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
          rfl
        · constructor
          · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, .inr rfl, ?_⟩
            intro output member
            cases member
          · intro output member
            cases member
    | some projectedFields =>
        rcases projectedFields with ⟨tries, residual⟩
        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, lower, reducing⟩ :=
          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
        obtain ⟨_prepared, middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, middleProtects⟩ := ownReceipt
        have observed := middleRun
        simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, Option.map_eq_some_iff] at observed
        obtain ⟨allocation, ownRun, endpoints⟩ := observed
        have sameMiddle : allocation.2 = middle := (Prod.mk.inj (List.cons.inj endpoints).1).2
        have ownObserved : SourcePruningEnumerationCachedOwn.suspendMany caller.checked.native.machine.heap tries before =
            some (allocation.1, middle) := by
          rw [← sameMiddle]
          exact ownRun
        obtain ⟨_ownSame, _cacheSame, _ownRaw, _counter, _forest, _safe, middleSlots,
            _oldProtection, _fresh⟩ :=
          SourceSynthesisProgramRolesClassAllocation.suspendMany_program_slots valid literal
            caller.checked.native.machine.heap tries before middle allocation.1 marked packet.safe slots ownObserved
        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
        let programIndex : Nat → Prop := fun index =>
          (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
            (edge.entry.key.symbol = literal "filter" ∧ index = 1)
        have inputAvoids : ∀ held, marked held → ∀ value bucket, (value, bucket) ∈ inputs →
            Avoids middle.core.representatives held bucket := by
          intro held tagged value bucket member
          exact (middleProtects held (slots.bounded held tagged) (slots.roots held tagged)
            (avoids held tagged)).2 value bucket member
        have inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
            ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
          intro sc member
          refine ⟨suspendedValid sc member, ?_⟩
          intro path represented
          obtain ⟨tail, same⟩ := annotationPaths sc member path represented
          exact ⟨tail, same.symm⟩
        have inputFields : ∀ index value bucket, inputs[index]? = some (value, bucket) → programIndex index →
            SourceSynthesisHereditaryProgramFields.ValueFields valid literal value ∧
              EnumerationSemantics.ValidSuspended bucket ∧
              SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket := by
          intro index value bucket selectedInput wanted
          obtain ⟨childFields, _inheritedEmpty, _ownBucket, bucketScope⟩ :=
            SourceSynthesisProgramChildScope.program_child_scope valid edge fields scs before.core.counter
              inherited tries residual projected index value bucket selectedInput wanted
          refine ⟨childFields, fun sc member => (bucketScope sc member).1, ?_⟩
          intro sc member path represented
          obtain ⟨tail, same⟩ := (bucketScope sc member).2 path represented
          exact ⟨tail, same.symm⟩
        have edgeBounds := (shapes parentEntry rows depth free available).2 edge selected
        have triesBound := edgeBounds.2 tries residual projected
        have inputLength : inputs.length ≤ limit := by
          simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using edgeBounds.1
        have inputFacts : ∀ value bucket, (value, bucket) ∈ inputs →
            Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
              bucket.length ≤ bound + own ∧ (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value bucket member
          obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine value bucket member
          have childRank := lower value bucket member
          obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
          cases same
          have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
          have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
            (suspendedVars before.core.counter tries)
          rw [SourcePruningEnumerationCostBounds.suspended_length] at added
          refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
            ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, by omega, ?_, childBounded, childPending⟩
          simp only [List.length_append]
          omega
        have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling := by
          rw [middleMass]
          exact mass
        let yes : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
          fun fuel fragments reached saved after =>
            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
              (.complete (.node edge.entry.key.symbol fragments) reached saved
                (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after))
        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
          fun fuel completed observation candidate =>
            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
              (.stopped completed observation candidate)
        have tupleConsumers : ProgramTupleConsumersWithOutputs outputOK valid literal marked programIndex formulas solver caller metadata middle inputs uv continuation admitted yes no := by
          constructor
          · intro fragments reached saved after history current retained fitted supported afterMass accepted
            obtain ⟨history, afterSlots, countSame, childRoles⟩ := history
            have originalData := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
              middleCore middleCounter middleProtects fragments reached saved after history
            have fragmentCount : fragments.length = edge.children.length := by
              simpa only [inputs, SourcePruningEnumerationEdgeInputs.children,
                List.length_map, List.length_zipIdx] using countSame
            have assembled := SourceSynthesisProgramParentCallbackRoles.fragment_roles_of_children valid marked edge
              fields fragments fragmentCount childRoles
            have finishedSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
                reached.checked.native.machine.heap
                (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after).core marked :=
              ⟨afterSlots.bounded, afterSlots.roots, afterSlots.incoming, afterSlots.stored⟩
            have data : ProgramChildInputs valid literal marked formulas solver caller metadata before scs
                (.node edge.entry.key.symbol fragments) reached saved
                (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after) :=
              ⟨originalData, finishedSlots, assembled⟩
            obtain ⟨fuel, outcome, running, resources⟩ := consumers.1 (.node edge.entry.key.symbol fragments)
              reached saved (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
              data current retained fitted supported afterMass accepted
            let receipt : SelectedEdge.Result (bits + 2) := .complete (.node edge.entry.key.symbol fragments)
              reached saved (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
            let result : Fold := match outcome with
              | .complete processed outputs finalCaller finalQueries => .complete (receipt :: processed) outputs finalCaller finalQueries
              | .stopped processed outputs stop => .stopped (receipt :: processed) outputs stop
            refine ⟨fuel, result, ?_, ?_⟩
            · intro extra
              change SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query
                (.complete (.node edge.entry.key.symbol fragments) reached saved
                  (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)) = result
              rw [SourcePruningEnumerationSharedEagerChildren.consume_complete, running extra]
              cases outcome <;> rfl
            · cases outcome <;> exact resources
          · intro completed reached saved after outer waiting next final post query _prefixRoles current retained fitted supported _accepted
            let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
              ((.ok (some []), reached, saved, outer, waiting)) (some after)
            let outcome : Fold := .complete [receipt] [] reached saved
            have resources : OutcomeResourcesWithOutputs outputOK formulas solver reached current (finish uv outcome) := by
              constructor
              · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                intro output member
                cases member
              · intro output member
                cases member
            have enlarged := growth retained current
            exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
        have tuple := eager_program_tuple_complete_of_child_with_outputs outputOK (Typing := Typing) (bits := bits)
          checkEmpty edgesOf captured limit own height formulas solver programChild limit
        obtain ⟨fuel, outcome, running, resources⟩ := tuple valid marked programIndex inventory caller memos metadata middle seed
          (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
          inputFacts middleSlots inputAvoids inputFields shapes selectionMembers selectionLength reserved growth tupleConsumers
        refine ⟨fuel, outcome, ?_, resources⟩
        intro extra
        rw [reducing]
        exact running extra
  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
    refine ⟨0, outcome, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
        SourcePruningEnumerationCachedOwn.prepare, allowed]
      rfl
    · constructor
      · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
        intro output member
        cases member
      · intro output member
        cases member

private theorem eager_program_selected_resources
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (programChild : EagerProgramChildComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
      SourceSynthesisLabelProgramBuildRoles.literal caller.checked.native.machine.heap before.core marked)
    (avoids : ∀ held, marked held → Avoids before.core.representatives held scs)
    (fields : SourceSynthesisHereditaryProgramFields.EdgeFields valid SourceSynthesisLabelProgramBuildRoles.literal edge)
    (suspendedValid : EnumerationSemantics.ValidSuspended scs)
    (annotationPaths : SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (consumers : ProgramChildConsumers valid SourceSynthesisLabelProgramBuildRoles.literal marked formulas solver caller metadata before scs uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitSelected
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query)
        scs edge caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome)
    := by
  simpa only [resources_outputs_true_iff] using
    (eager_program_selected_resources_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver valid marked
      (by simpa only [EagerProgramChildCompleteWithOutputs, EagerProgramChildComplete, ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using programChild) inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped packet fits known kept mass bucketBound parentEntry rows depth free available closed ranked edge selected bounded pending slots avoids fields suspendedValid annotationPaths shapes selectionMembers selectionLength reserved growth
      (by simpa only [ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using consumers))

end ActualProgramSelectedResources

section ActualProgramRowsConsumers
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem program_child_consumers_post_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original middle : Caller (bits + 2)) (next : Inventory) (final : Memos)
    (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (earlier : Post formulas solver next original middle final)
    (consumers : ProgramChildConsumersWithOutputs outputOK valid literal marked formulas solver original metadata before bucket uv continuation admitted done stopped) :
    ProgramChildConsumersWithOutputs outputOK valid literal marked formulas solver middle metadata before bucket uv continuation admitted done stopped := by
  constructor
  · intro fragment reached saved after data current retained fitted supported mass accepted
    obtain ⟨data, slots, roles⟩ := data
    obtain ⟨next, final, post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩ := data
    exact consumers.1 fragment reached saved after
      ⟨⟨next, final, earlier.trans post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩,
        slots, roles⟩
      current retained fitted supported mass accepted
  · intro reached saved after outer waiting next final post query current retained fitted supported accepted
    exact consumers.2 reached saved after outer waiting next final (earlier.trans post) query
      current retained fitted supported accepted

private theorem program_child_consumers_post
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original middle : Caller (bits + 2)) (next : Inventory) (final : Memos)
    (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (earlier : Post formulas solver next original middle final)
    (consumers : ProgramChildConsumers valid literal marked formulas solver original metadata before bucket uv continuation admitted done stopped) :
    ProgramChildConsumers valid literal marked formulas solver middle metadata before bucket uv continuation admitted done stopped := by
  simpa only [ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using
    (program_child_consumers_post_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) valid literal marked formulas solver original middle next final metadata before bucket uv continuation admitted done stopped earlier
      (by simpa only [ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using consumers))
end ActualProgramRowsConsumers

section ActualProgramRowsResources
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def EagerProgramRowsCompleteWithOutputs
    (outputOK : Output (bits + 2) Typing → Prop) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  let literal := SourceSynthesisLabelProgramBuildRoles.literal
  ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    (∀ held, marked held → Avoids before.core.representatives held scs) →
    (∀ edge ∈ rows, SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge) →
    EnumerationSemantics.ValidSuspended scs →
    SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed index)) →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ProgramChildConsumersWithOutputs outputOK valid literal marked formulas solver caller metadata before scs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) reached saved)
          scs edge reached cached saved) before alternatives caller memos.query = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed count) (finish uv outcome)

private def EagerProgramRowsComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  let literal := SourceSynthesisLabelProgramBuildRoles.literal
  ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    (∀ held, marked held → Avoids before.core.representatives held scs) →
    (∀ edge ∈ rows, SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge) →
    EnumerationSemantics.ValidSuspended scs →
    SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed index)) →
    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
    ProgramChildConsumers valid literal marked formulas solver caller metadata before scs uv continuation admitted done stopped →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) reached saved)
          scs edge reached cached saved) before alternatives caller memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height)
          limit (bound + own) ceiling continuation current) seed count) (finish uv outcome)

private theorem eager_program_rows_complete_of_child_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (programChild : EagerProgramChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerProgramRowsCompleteWithOutputs outputOK (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
  let literal : String → Symbol := SourceSynthesisLabelProgramBuildRoles.literal
  induction count with
  | zero =>
      intro valid marked inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped
        packet fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending
        _slots _avoids _rowFields _suspendedValid _annotationPaths alternatives length _selected _shapes _selectionMembers _selectionLength _reserved growth _consumers
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl,
            fun _ member => by cases member⟩, fun _ member => by cases member⟩
  | succ count ih =>
      intro valid marked inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped
        packet fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending
        slots avoids rowFields suspendedValid annotationPaths alternatives length selected shapes selectionMembers selectionLength reserved growth consumers
      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      cases alternatives with
      | nil =>
          have enlarged := iterate_ge row rowGrowth seed (count + 1)
          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
              caller.checked.native.machine.heap := by
            intro key edge found
            exact enlarged.2 (known key edge found)
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
            supported, rfl, rfl, fun _ member => by cases member⟩, fun _ member => by cases member⟩
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_program_selected_resources_with_outputs outputOK
            checkEmpty edgesOf captured limit own height formulas solver valid marked programChild inventory caller memos metadata before seed
            bound ceiling scs uv continuation admitted done stopped packet fits known kept mass bucketBound
            parentEntry rows depth free available closed ranked edge (selected edge (by simp)) bounded pending slots avoids (rowFields edge (selected edge (by simp)))
            suspendedValid annotationPaths shapes selectionMembers selectionLength firstReserved growth consumers
          have farther := iterate_ge row rowGrowth (row seed) count
          cases headOutcome with
          | stopped processed outputs current =>
              refine ⟨headFuel, .stopped processed outputs current, ?_, resources_outputs_mono farther.1 farther.2 headResources⟩
              intro extra
              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
          | complete processed outputs reached saved =>
              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, _outputResources⟩ :=
                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources.1
              have laterReserved : ∀ index, index < count →
                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
                intro index inside
                exact reserved (index + 1) (by omega)
              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              have reachedSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
                caller.checked.native.machine.heap reached.checked.native.machine.heap before.core marked post.effects.keeps slots
              have reachedConsumers := program_child_consumers_post_with_outputs outputOK valid literal marked formulas solver caller reached next final metadata before scs uv
                continuation admitted done stopped post consumers
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih valid marked next reached final metadata before (row seed)
                bound ceiling scs uv continuation admitted done stopped reachedPacket reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending reachedSlots avoids rowFields suspendedValid annotationPaths
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved growth reachedConsumers
              let result : Fold := match (generalizing := false) tailOutcome with
                | .complete later remaining finalCaller finalQueries =>
                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
              · intro extra
                have headAt := headRunning (tailFuel + extra)
                have tailAt := tailRunning (headFuel + extra)
                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
                rw [hs] at headAt
                rw [ts, query] at tailAt
                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
                dsimp only
                rw [tailAt]
                cases tailOutcome <;> rfl
              · simpa only [SourcePruningEnumerationFiniteReservation.iterate_succ, row, result] using
                  (resources_outputs_append uv processed outputs tailOutcome post farther.1 farther.2
                    (by simpa only [query, finish, row] using headResources) tailResources)

private theorem eager_program_rows_complete_of_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (programChild : EagerProgramChildComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerProgramRowsComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver
    := by
  simpa only [EagerProgramRowsCompleteWithOutputs, EagerProgramRowsComplete, ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using
    (eager_program_rows_complete_of_child_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver
      (by simpa only [EagerProgramChildCompleteWithOutputs, EagerProgramChildComplete, ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using programChild) count)
end ActualProgramRowsResources

section ActualProgramEmptyResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_empty_resources_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (limit own height bound ceiling : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (reserved : nodeReserved bits limit own height bound ceiling continuation admitted seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (consumers : ProgramChildConsumersWithOutputs outputOK valid SourceSynthesisLabelProgramBuildRoles.literal marked formulas solver
      caller metadata before bucket uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket .empty caller
        before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResourcesWithOutputs outputOK formulas solver caller
        (nodePlan limit own height bound ceiling continuation seed) (finish uv outcome) := by
  have fallback := nodeReserved_fallback bits limit own height bound ceiling continuation admitted seed reserved
  have paddedFits : Fits (advance seed (bound + 1)).2 caller.checked := fits.mono
    (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed (bound + 1))
  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
      caller.checked.native.machine.heap := by
    intro key edge found
    exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge seed (bound + 1) (known key edge found)
  obtain ⟨fuel, outcome, running, resources⟩ := consumers.2 caller memos.query before before.core before.waiting
    inventory memos (Post.refl packet.context) rfl (advance seed (bound + 1)) (ceiling + bound)
    paddedFits paddedKnown fallback.2
  have included := fallbackPlan_le_nodePlan limit own height bound ceiling continuation growth seed
  refine ⟨fuel, outcome, ?_, resources_outputs_mono included.1 included.2 resources⟩
  intro extra
  rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty
    (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket .empty caller
    before memos.query (done (fuel + extra)) (stopped (fuel + extra)) rfl]
  simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit,
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run, ↓reduceIte] using running extra

private theorem eager_program_empty_resources
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (limit own height bound ceiling : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (bucket : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (reserved : nodeReserved bits limit own height bound ceiling continuation admitted seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (consumers : ProgramChildConsumers valid SourceSynthesisLabelProgramBuildRoles.literal marked formulas solver
      caller metadata before bucket uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket .empty caller
        before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
      OutcomeResources formulas solver caller
        (nodePlan limit own height bound ceiling continuation seed) (finish uv outcome)
    := by
  simpa only [resources_outputs_true_iff] using
    (eager_program_empty_resources_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf limit own height bound ceiling seed formulas solver valid marked inventory caller memos metadata before bucket uv continuation admitted done stopped packet fits known reserved growth
      (by simpa only [ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using consumers))
end ActualProgramEmptyResources

private theorem eager_program_annotation_nonterminal
    (scs : List Suspended)
    (scope : SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs) :
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
  apply List.any_eq_false.mpr
  intro sc member tagged
  have terminal : sc.trie = .terminal := by
    cases trieRead : sc.trie with
    | empty => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
    | terminal => rfl
    | branch children => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
  obtain ⟨tail, impossible⟩ := scope sc member [] ((EqualityTrie.nil_mem sc.trie).mpr terminal)
  cases impossible

section ActualProgramHeightResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_child_height_complete_with_outputs
    (outputOK : Output (bits + 2) Typing → Prop)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerProgramChildCompleteWithOutputs outputOK (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver := by
  induction height with
  | zero =>
      intro valid marked inventory caller memos metadata before seed bound ceiling bucket incoming uv continuation admitted done stopped
        packet fits known available kept closed bounded pending mass bucketBound ranked slots avoids fields suspendedValid
        annotationPaths shapes selectionMembers selectionLength reserved growth consumers
      cases fields with
      | empty =>
          exact eager_program_empty_resources_with_outputs outputOK checkEmpty edgesOf limit own 0 bound ceiling seed formulas solver valid marked
            inventory caller memos metadata before bucket uv continuation admitted done stopped packet fits known reserved growth consumers
      | node entry rows depth free rowFields =>
          simp only [MergedOrdinaryHeight.height] at ranked
          omega
  | succ height ih =>
      intro valid marked inventory caller memos metadata before seed bound ceiling bucket incoming uv continuation admitted done stopped
        packet fits known available kept closed bounded pending mass bucketBound ranked slots avoids fields suspendedValid
        annotationPaths shapes selectionMembers selectionLength reserved growth consumers
      cases fields with
      | empty =>
          exact eager_program_empty_resources_with_outputs outputOK checkEmpty edgesOf limit own (height + 1) bound ceiling seed formulas solver valid marked
            inventory caller memos metadata before bucket uv continuation admitted done stopped packet fits known reserved growth consumers
      | node entry rows depth free rowFields =>
          have nonterminal := eager_program_annotation_nonterminal bucket annotationPaths
          have ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket
              (.node entry rows depth free) = true := by
            simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal, nonterminal]
          let first := fallbackPlan bound ceiling continuation seed
          have initial := fallbackPlan_ge bound ceiling continuation growth seed
          have firstFits : Fits first.2 caller.checked := fits.mono initial.1
          have firstKnown : Heap (fun guard => guard ∈ first.1) caller.checked.native.machine.heap := by
            intro key edge found
            exact initial.2 (known key edge found)
          have alternativesLength : (edgesOf (.node entry rows depth free)).length ≤ limit :=
            Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
          have rowsComplete := eager_program_rows_complete_of_child_with_outputs outputOK (Typing := Typing) (bits := bits)
            checkEmpty edgesOf captured limit own height formulas solver ih limit
          obtain ⟨fuel, outcome, running, resources⟩ := rowsComplete valid marked inventory caller memos metadata before first
            bound ceiling bucket uv continuation admitted done stopped packet firstFits firstKnown kept mass bucketBound
            entry rows depth free available closed ranked bounded pending slots avoids rowFields suspendedValid annotationPaths
            (edgesOf (.node entry rows depth free))
            alternativesLength (selectionMembers entry rows depth free) shapes selectionMembers selectionLength reserved.2 growth consumers
          refine ⟨fuel, outcome, ?_, resources⟩
          intro extra
          let work := fuel + extra
          let full : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold :=
            fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
              (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
              bucket edge reached cached saved
          let guarded : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold :=
            fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
              (fun inherited child current cache memos yes no =>
                if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node entry rows depth free) then
                  SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf
                    inherited child current cache memos yes no
                else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty work work work work work
                  inherited child current cache memos yes no)
              (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
              bucket edge reached cached saved
          have same : SourcePruningEnumerationSharedBranching.scan guarded before
              (edgesOf (.node entry rows depth free)) caller memos.query =
              SourcePruningEnumerationSharedBranching.scan full before
                (edgesOf (.node entry rows depth free)) caller memos.query := by
            apply scan_members_congr
            intro edge member reached saved
            exact selected_guarded_eq checkEmpty work work work work work edgesOf entry rows depth free
              edge (selectionMembers entry rows depth free edge member) bucket reached before saved
              (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
          have sourceRun := SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary checkEmpty
            work work work work work edgesOf bucket (.node entry rows depth free) caller before memos.query
            (done work) (stopped work) ordinary
          exact sourceRun.trans (same.trans (running extra))

private theorem eager_program_child_height_complete
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerProgramChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver
    := by
  simpa only [EagerProgramChildCompleteWithOutputs, EagerProgramChildComplete, ProgramChildConsumersWithOutputs, ProgramChildConsumers, resources_outputs_true_iff] using
    (eager_program_child_height_complete_with_outputs (Typing := Typing) (bits := bits) (fun _ => True) checkEmpty edgesOf captured limit own height formulas solver)
end ActualProgramHeightResources

section ActualFinalizedProgramCallback
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem finalized_program_callback_observation
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing) (before middle : Cached)
    (uv handle : Nat) (scs : List Suspended) (fragment : Fragment) (saved : Queries)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core) (selected : marked uv)
    (data : ProgramChildInputs valid SourceSynthesisLabelProgramBuildRoles.literal marked
      formulas solver original metadata before scs fragment reached saved middle)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (seed : Seed)
    (bounded : Fits seed.2 reached.checked)
    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) :
    ∃ (next : Inventory) (final : Memos) (finalizeFuel : Nat) (finalized : Cached)
      (callbackFuel : Nat) (result : Bool × Metadata Typing) (afterCore : EnumerationState.State Symbol Constraint),
      (Post formulas solver next original reached final ∧ final.query = saved ∧
      (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        (finalizeFuel + extra) uv fragment middle = some finalized) ∧
      Packet formulas solver next reached final metadata finalized ∧
      FragmentBound finalized.core.counter fragment ∧
      finalized.core = {middle.core with values := middle.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound finalized.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ∧
      finalized.core.values[uv]? = some (.enumerated fragment) ∧ IsRoot finalized.core.representatives uv) ∧
      (Packet formulas solver next reached final result.2 (EnumerationExpandableIndex.frame afterCore finalized) ∧
      EnumerationDriver.RenderStable finalized.core afterCore ∧
      EnumerationCompressionFrame.Frame finalized.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          finalized.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) finalized.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment reached final.query finalized =
            if result.1 then .complete [] reached final.query
            else recur result.2 reached final.query (EnumerationExpandableIndex.frame afterCore finalized)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore finalized))) ∧
      SourceSynthesisProgramEnumerationRoles.FragmentRoles SourceSynthesisLabelProgramBuildRoles.literal marked fragment ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap finalized.core marked ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap (EnumerationExpandableIndex.frame afterCore finalized).core marked ∧
      ∀ extra (initialCaller : Caller (bits + 2)) (initialQueries : Queries)
        (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
          NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
        let work := finalizeFuel + callbackFuel + extra
        let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finalized
        let callbackResult : NativeContinuations.HookResult
            (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
          if result.1 then .complete [] reached saved
          else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
            (SourcePruningEnumerationRestart.decision stop order result.2
              (EnumerationExpandableIndex.frame afterCore finalized))
        (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.complete fragment reached saved finished))
        | none => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.finalizeStopped fragment reached saved middle))) =
        match callbackResult with
        | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
        | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
    := by
  obtain ⟨next, final, finalizeFuel, finalized, finalReceipt⟩ :=
    finalize_child_inputs_packet formulas solver original reached metadata before middle uv handle scs fragment saved
      ready stored incoming data.1
  have retained := finalReceipt
  obtain ⟨_post, querySame, finalAt, finalPacket, fragmentBound, core, _mass, _stored, _root⟩ := retained
  let writtenCore := {middle.core with values := middle.core.values.set uv (.enumerated fragment)}
  have written : Success (EnumerationState.setValue uv (.enumerated fragment)) middle.core () writtenCore :=
    (EnumerationDriver.modify_success _ _ _).mpr rfl
  have writtenSlots := (SourceSynthesisProgramFragmentWrite.setValue_program_slots valid
    SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap middle.core writtenCore
    marked data.2.1 uv selected fragment data.2.2 written).2
  have finalizedSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
      SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap finalized.core marked := by
    rw [core]
    exact ⟨writtenSlots.bounded, writtenSlots.roots, writtenSlots.incoming, writtenSlots.stored⟩
  obtain ⟨callbackFuel, result, afterCore, callback⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver next graph templates
      metadata uv fragment reached final finalized seed finalPacket fragmentBound bounded known
  have callbackFields := callback
  obtain ⟨_callbackPacket, _stable, callbackFrame, _types, _holes, _typing, _fits, _known, callbackAt⟩ := callbackFields
  have callbackSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
    reached.checked.native.machine.heap finalized.core afterCore marked callbackFrame finalizedSlots
  refine ⟨next, final, finalizeFuel, finalized, callbackFuel, result, afterCore,
    finalReceipt, callback, data.2.2, finalizedSlots, callbackSlots, ?_⟩
  intro extra initialCaller initialQueries recur stop order
  have finalizeAt := finalAt (callbackFuel + extra)
  rw [← Nat.add_assoc] at finalizeAt
  have continued := (callbackAt (finalizeFuel + extra)).2.2 recur stop order
  have same : callbackFuel + (finalizeFuel + extra) = finalizeFuel + callbackFuel + extra := by omega
  rw [same, querySame] at continued
  dsimp only
  rw [finalizeAt]
  simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
  rw [continued]
  cases observed : (if result.1 then NativeContinuations.HookResult.complete [] reached saved
      else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
        (SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame afterCore finalized))) <;> rfl

end ActualFinalizedProgramCallback

section ConcreteEagerProgramResumeZero
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

-- Proposed PRIVATE definition in SharedEagerReservation. Existing aliases, Key and Eq scope apply.
private def EagerProgramResumeComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    eagerReserved bits recursiveDepth seed ceiling →
    ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked →
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (bound + extra) (bound + extra)
          (bound + extra) (bound + extra) (bound + extra) edgesOf)
        holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveDepth
        metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked)
        formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome

/-- The concrete resume observer retains Program roles and original isolated markers. -/
private def EagerProgramResumeWithIsolatedComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    eagerReserved bits recursiveDepth seed ceiling →
    ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked →
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (bound + extra) (bound + extra)
          (bound + extra) (bound + extra) (bound + extra) edgesOf)
        holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveDepth
        metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRolesWithIsolated valid marked caller before)
        formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome

-- Direct-emission leaf: current concrete slots, no arbitrary output predicate.
omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem program_output_roles_current
    (valid : Constraint → Prop) (marked : Nat → Prop) (output : Output (bits + 2) Typing)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      output.caller.checked.native.machine.heap output.cache.core marked) :
    programOutputRoles valid marked output := by
  exact ⟨marked, fun _ tagged => tagged, slots⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- A literal emission from the current cache retains both output properties. -/
private theorem program_output_roles_with_isolated_current
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (metadata : Option (Metadata Typing))
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
      SourceSynthesisLabelProgramBuildRoles.literal caller.checked.native.machine.heap before.core marked) :
    programOutputRolesWithIsolated valid marked caller before ⟨metadata, before, caller, queries⟩
 := by
  refine ⟨program_output_roles_current valid marked _ slots, ?_⟩
  intro held handle value isolated decoded _boundary
  exact ⟨isolated, decoded⟩

private theorem eager_program_resume_zero_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerProgramResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength mass reserved valid marked slots
  obtain ⟨bound, outcome, running, resources⟩ :=
    (eager_resume_zero_complete holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver) inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength mass reserved
  refine ⟨bound, outcome, running, resources, ?_⟩
  intro output member
  have observed := running 0
  generalize _decision : SourcePruningEnumerationRestart.decision stop order metadata before = selected at observed
  cases selected with
  | none =>
      rw [← observed] at member
      change output ∈ [⟨some metadata, before, caller, memos.query⟩] at member
      rcases List.mem_singleton.mp member with rfl
      exact program_output_roles_current valid marked _ slots
  | some selected =>
      cases selected with
      | done =>
          rw [← observed] at member
          change output ∈ [⟨none, before, caller, memos.query⟩] at member
          rcases List.mem_singleton.mp member with rfl
          exact program_output_roles_current valid marked _ slots
      | stuck =>
          rw [← observed] at member
          change output ∈ ([] : List (Output (bits + 2) Typing)) at member
          cases member
      | expand _uv =>
          rw [← observed] at member
          change output ∈ ([] : List (Output (bits + 2) Typing)) at member
          cases member
/-- At depth zero, the same emitted cache retains both concrete output properties. -/
private theorem eager_program_resume_zero_with_isolated_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerProgramResumeWithIsolatedComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength mass reserved valid marked slots
  obtain ⟨bound, outcome, running, resources⟩ :=
    (eager_program_resume_zero_complete holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver) inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength mass reserved valid marked slots
  refine ⟨bound, outcome, running, resources.1, ?_⟩
  intro output member
  have observed := running 0
  generalize _decision : SourcePruningEnumerationRestart.decision stop order metadata before = selected at observed
  cases selected with
  | none =>
      rw [← observed] at member
      change output ∈ [⟨some metadata, before, caller, memos.query⟩] at member
      rcases List.mem_singleton.mp member with rfl
      exact program_output_roles_with_isolated_current valid marked caller before memos.query
        (some metadata) slots
  | some selected =>
      cases selected with
      | done =>
          rw [← observed] at member
          change output ∈ [⟨none, before, caller, memos.query⟩] at member
          rcases List.mem_singleton.mp member with rfl
          exact program_output_roles_with_isolated_current valid marked caller before memos.query
            none slots
      | stuck =>
          rw [← observed] at member
          change output ∈ ([] : List (Output (bits + 2) Typing)) at member
          cases member
      | expand _uv =>
          rw [← observed] at member
          change output ∈ ([] : List (Output (bits + 2) Typing)) at member
          cases member
end ConcreteEagerProgramResumeZero

section ActualFinalizedUnmarkedCallback
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem finalized_unmarked_callback_observation
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing) (before middle : Cached)
    (uv handle : Nat) (scs : List Suspended) (fragment : Fragment) (saved : Queries)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core) (unmarked : ¬marked uv)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      original.checked.native.machine.heap before.core marked)
    (data : ChildInputs formulas solver original metadata before scs fragment reached saved middle)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (seed : Seed)
    (bounded : Fits seed.2 reached.checked)
    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) :
    ∃ (next : Inventory) (final : Memos) (finalizeFuel : Nat) (finalized : Cached)
      (callbackFuel : Nat) (result : Bool × Metadata Typing) (afterCore : EnumerationState.State Symbol Constraint),
      (Post formulas solver next original reached final ∧ final.query = saved ∧
      (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        (finalizeFuel + extra) uv fragment middle = some finalized) ∧
      Packet formulas solver next reached final metadata finalized ∧
      FragmentBound finalized.core.counter fragment ∧
      finalized.core = {middle.core with values := middle.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound finalized.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ∧
      finalized.core.values[uv]? = some (.enumerated fragment) ∧ IsRoot finalized.core.representatives uv) ∧
      (Packet formulas solver next reached final result.2 (EnumerationExpandableIndex.frame afterCore finalized) ∧
      EnumerationDriver.RenderStable finalized.core afterCore ∧
      EnumerationCompressionFrame.Frame finalized.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          finalized.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) finalized.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment reached final.query finalized =
            if result.1 then .complete [] reached final.query
            else recur result.2 reached final.query (EnumerationExpandableIndex.frame afterCore finalized)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore finalized))) ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap finalized.core marked ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap (EnumerationExpandableIndex.frame afterCore finalized).core marked ∧
      ∀ extra (initialCaller : Caller (bits + 2)) (initialQueries : Queries)
        (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
          NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
        let work := finalizeFuel + callbackFuel + extra
        let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finalized
        let callbackResult : NativeContinuations.HookResult
            (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
          if result.1 then .complete [] reached saved
          else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
            (SourcePruningEnumerationRestart.decision stop order result.2
              (EnumerationExpandableIndex.frame afterCore finalized))
        (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.complete fragment reached saved finished))
        | none => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.finalizeStopped fragment reached saved middle))) =
        match callbackResult with
        | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
        | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)

    := by
  have inherited : ∀ held, marked held → Avoids before.core.representatives held scs := by
    intro held heldMarked
    exact slots.incoming held heldMarked (.unenumerated (some handle) scs)
      (List.mem_of_getElem? stored)
  have middleSlots := child_inputs_program_slots valid SourceSynthesisLabelProgramBuildRoles.literal marked
    formulas solver original reached metadata before middle scs fragment saved ready.safe slots inherited data
  obtain ⟨next, final, finalizeFuel, finalized, finalReceipt⟩ :=
    finalize_child_inputs_packet formulas solver original reached metadata before middle uv handle scs fragment saved
      ready stored incoming data
  have retained := finalReceipt
  obtain ⟨_post, querySame, finalAt, finalPacket, fragmentBound, core, _mass, _stored, _root⟩ := retained
  let resetCore := {middle.core with expansionAncestry := []}
  have resetSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
      SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap resetCore marked :=
    ⟨middleSlots.bounded, middleSlots.roots, middleSlots.incoming, middleSlots.stored⟩
  have written : Success (EnumerationState.setValue uv (.enumerated fragment)) resetCore () finalized.core :=
    (EnumerationDriver.modify_success _ _ _).mpr core
  have finalizedSlots := (SourceSynthesisProgramRolesUnmarkedWrite.setValue_unmarked_program_slots valid
    SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap resetCore finalized.core
    marked resetSlots uv unmarked (.enumerated fragment) (by intro _ _ _ member; cases member) written).2.1
  obtain ⟨callbackFuel, result, afterCore, callback⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver next graph templates
      metadata uv fragment reached final finalized seed finalPacket fragmentBound bounded known
  have callbackFields := callback
  obtain ⟨_callbackPacket, _stable, callbackFrame, _types, _holes, _typing, _fits, _known, callbackAt⟩ := callbackFields
  have callbackSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
    reached.checked.native.machine.heap finalized.core afterCore marked callbackFrame finalizedSlots
  refine ⟨next, final, finalizeFuel, finalized, callbackFuel, result, afterCore,
    finalReceipt, callback, finalizedSlots, callbackSlots, ?_⟩
  intro extra initialCaller initialQueries recur stop order
  have finalizeAt := finalAt (callbackFuel + extra)
  rw [← Nat.add_assoc] at finalizeAt
  have continued := (callbackAt (finalizeFuel + extra)).2.2 recur stop order
  have same : callbackFuel + (finalizeFuel + extra) = finalizeFuel + callbackFuel + extra := by omega
  rw [same, querySame] at continued
  dsimp only
  rw [finalizeAt]
  simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
  rw [continued]
  cases observed : (if result.1 then NativeContinuations.HookResult.complete [] reached saved
      else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
        (SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame afterCore finalized))) <;> rfl

end ActualFinalizedUnmarkedCallback

section ActualRecordedProgramCallback
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_callback_from_recorded_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (_allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing)
    (afterCore : EnumerationState.State Symbol Constraint)
    (recorded :
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame afterCore before) ∧
      EnumerationDriver.RenderStable before.core afterCore ∧
      EnumerationCompressionFrame.Frame before.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          before.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) before.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame afterCore before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore before))) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith (recur (fuel + extra))
      graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
    OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
      (eagerFinal recursiveDepth seed ceiling) outcome
  obtain ⟨returned, _stable, frame, _types, _holes, _typing, _currentFits, _currentKnown, callback⟩ := recorded
  by_cases rejected : result.1 = true
  · have retained : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked) formulas solver caller seed
        (.complete [] caller memos.query) := by
      exact ⟨retained, fun _ member => by cases member⟩
    have growth := eagerFinal_ge recursiveDepth seed ceiling
    refine ⟨callbackFuel, .complete [] caller memos.query, ?_,
      resources_outputs_mono growth.1 growth.2 resources⟩
    intro extra
    rw [(callback extra).2.2 (recur (callbackFuel + extra)) stop order, ite_eq_left rejected]
  · have afterSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      caller.checked.native.machine.heap before.core afterCore marked frame slots
    have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
        (EnumerationExpandableIndex.frame afterCore before).core ≤ ceiling := by
      change SourcePruningEnumerationPrefixAdmission.suspendedBound afterCore ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core afterCore frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame afterCore before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved valid marked afterSlots
    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources⟩
    intro extra
    have actual := callback (resumeFuel + extra)
    rw [← Nat.add_assoc] at actual
    rw [actual.2.2 (recur (callbackFuel + resumeFuel + extra)) stop order, ite_eq_right rejected]
    have observed := running (callbackFuel + extra)
    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
    rw [common] at observed
    exact observed

/-- The recorded callback retains roles and isolated markers from its original cache. -/
private theorem eager_program_callback_from_recorded_resources_with_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeWithIsolatedComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (_allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing)
    (afterCore : EnumerationState.State Symbol Constraint)
    (recorded :
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame afterCore before) ∧
      EnumerationDriver.RenderStable before.core afterCore ∧
      EnumerationCompressionFrame.Frame before.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          before.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) before.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame afterCore before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore before))) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRolesWithIsolated valid marked caller before) formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith (recur (fuel + extra))
      graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
    OutcomeResourcesWithOutputs (programOutputRolesWithIsolated valid marked caller before) formulas solver caller
      (eagerFinal recursiveDepth seed ceiling) outcome
  obtain ⟨returned, _stable, frame, _types, _holes, _typing, _currentFits, _currentKnown, callback⟩ := recorded
  by_cases rejected : result.1 = true
  · have retained : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRolesWithIsolated valid marked caller before) formulas solver caller seed
        (.complete [] caller memos.query) := by
      exact ⟨retained, fun _ member => by cases member⟩
    have growth := eagerFinal_ge recursiveDepth seed ceiling
    refine ⟨callbackFuel, .complete [] caller memos.query, ?_,
      resources_outputs_mono growth.1 growth.2 resources⟩
    intro extra
    rw [(callback extra).2.2 (recur (callbackFuel + extra)) stop order, ite_eq_left rejected]
  · have afterSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      caller.checked.native.machine.heap before.core afterCore marked frame slots
    have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
        (EnumerationExpandableIndex.frame afterCore before).core ≤ ceiling := by
      change SourcePruningEnumerationPrefixAdmission.suspendedBound afterCore ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core afterCore frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame afterCore before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved valid marked afterSlots
    have rebased : OutcomeResourcesWithOutputs
        (programOutputRolesWithIsolated valid marked caller before) formulas solver caller
        (eagerFinal recursiveDepth seed ceiling) outcome := by
      refine ⟨resources.1, ?_⟩
      intro output member
      obtain ⟨roles, markers⟩ := resources.2 output member
      refine ⟨roles, ?_⟩
      intro held handle value isolated decoded boundary
      have moved : EnumerationDischargeHistory.IsolatedPending held handle
          (EnumerationExpandableIndex.frame afterCore before).core :=
        isolated.through_frame frame
      exact markers held handle value moved decoded boundary
    refine ⟨callbackFuel + resumeFuel, outcome, ?_, rebased⟩
    intro extra
    have actual := callback (resumeFuel + extra)
    rw [← Nat.add_assoc] at actual
    rw [actual.2.2 (recur (callbackFuel + resumeFuel + extra)) stop order, ite_eq_right rejected]
    have observed := running (callbackFuel + extra)
    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
    rw [common] at observed
    exact observed

end ActualRecordedProgramCallback

section ActualProgramOpaqueResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (unmarked : ¬marked uv) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
  have cost : scs.length + 1 ≤ bound + 1 := by omega
  obtain ⟨headFuel, receipt, reached, saved, final, next, headReceipt, headRoles⟩ :=
    SourceSynthesisProgramRolesOpaque.opaque_complete_resources_program_slots seed formulas solver inventory
      caller memos metadata before checkEmpty uv handle scs value packet ready stored incoming available closed
      dispatch fits (reserved.1.prefix cost) known valid marked slots unmarked
  obtain ⟨headRun, headPost, headQuery, _advanced, admitted, _pending, _history,
    headFits, headKnown, shape, _finalization⟩ := headReceipt
  have padding : Le (advance seed (scs.length + 1)).2 (advance seed (bound + 1)).2 ∧
      (advance seed (scs.length + 1)).1 ⊆ (advance seed (bound + 1)).1 :=
    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed cost,
      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed cost⟩
  have paddedFits := headFits.mono padding.1
  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
      reached.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
  subst saved
  rcases shape with completed | stopped | rejected
  · obtain ⟨fragment, after, rfl, afterPacket, _counter, afterMass⟩ := completed
    have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound := by omega
    have afterSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
        SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap after.core marked := headRoles
    obtain ⟨recordedFuel, result, afterCore, recorded⟩ :=
      SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver next graph templates
        metadata uv fragment reached final after (advance seed (bound + 1)) afterPacket admitted.2.2.1
        paddedFits paddedKnown
    obtain ⟨callbackFuel, continued, callbackRun, resources⟩ :=
      eager_program_callback_from_recorded_resources holeKey keyMatches admits formulas solver next graph templates metadata uv
        fragment reached final after checkEmpty edgesOf stop order recursiveDepth recursive
        (advance seed (bound + 1)) (ceiling + bound) afterPacket admitted.2.2.1 paddedFits paddedKnown
        selectionMembers selectionLength actualMass reserved.2 valid marked afterSlots recordedFuel result afterCore recorded
    let folded : Fold := match continued with
      | .complete outputs actual queries =>
          .complete [.complete fragment reached final.query after] outputs actual queries
      | .stopped outputs reason endpoint =>
          .stopped [] outputs (.continuation (.complete fragment reached final.query after) reason endpoint)
    have fullResources := resources_outputs_post headPost resources
    have finished : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed)
        (finish uv folded) := by
      cases continued <;>
        simpa only [folded, finish, SourcePruningEnumerationSharedPreparedRecursive.endpoint,
          OutcomeResourcesWithOutputs, OutcomeResources, fallbackPlan,
          SourcePruningEnumerationSharedPreparedRecursive.emitted] using fullResources
    refine ⟨headFuel + callbackFuel, .complete fragment reached final.query after, folded, ?_, ?_, finished⟩
    · intro extra
      have actual := headRun (callbackFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callbackRun (headFuel + extra)
      have common : callbackFuel + (headFuel + extra) = headFuel + callbackFuel + extra := by omega
      rw [common] at actual
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual]
      cases continued <;> rfl
  · obtain ⟨after, outer, waiting, rfl, _counter, _mass⟩ := stopped
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked)
        formulas solver caller (advance seed (bound + 1)) (.complete [] reached final.query) := by
      refine ⟨?_, fun _ member => by cases member⟩
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    refine ⟨headFuel, .stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after),
      .complete [.stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after)] [] reached final.query,
      headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · simpa only [finish, fallbackPlan] using resources_outputs_mono growth.1 growth.2 resources
  · subst receipt
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked)
        formulas solver caller (advance seed (bound + 1)) (.complete [] reached final.query) := by
      refine ⟨?_, fun _ member => by cases member⟩
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    have endpoints : (caller, memos.query) = (reached, final.query) := by
      exact Option.some.inj _advanced
    obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
    refine ⟨headFuel, .rejected caller memos.query before,
      .complete [.rejected caller memos.query before] [] caller memos.query, headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · have fullResources := resources_outputs_mono growth.1 growth.2 resources
      simpa only [finish, fallbackPlan, callerSame, querySame] using fullResources

/-- The opaque receipt retains roles and isolated markers outside its written target. -/
private theorem eager_program_opaque_resources_with_isolated_except
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeWithIsolatedComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (unmarked : ¬marked uv) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
  have cost : scs.length + 1 ≤ bound + 1 := by omega
  obtain ⟨headFuel, receipt, reached, saved, final, next, headReceipt, headRoles⟩ :=
    SourceSynthesisProgramRolesOpaque.opaque_complete_resources_program_slots seed formulas solver inventory
      caller memos metadata before checkEmpty uv handle scs value packet ready stored incoming available closed
      dispatch fits (reserved.1.prefix cost) known valid marked slots unmarked
  obtain ⟨headRun, headPost, headQuery, _advanced, admitted, _pending, _history,
    headFits, headKnown, shape, finalization⟩ := headReceipt
  have padding : Le (advance seed (scs.length + 1)).2 (advance seed (bound + 1)).2 ∧
      (advance seed (scs.length + 1)).1 ⊆ (advance seed (bound + 1)).1 :=
    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed cost,
      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed cost⟩
  have paddedFits := headFits.mono padding.1
  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
      reached.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
  subst saved
  rcases shape with completed | stopped | rejected
  · obtain ⟨fragment, after, rfl, afterPacket, _counter, afterMass⟩ := completed
    have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound := by omega
    have afterSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
        SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap after.core marked := headRoles
    obtain ⟨middle, outer, waiting, childRun, finalRun, _finalMeaning⟩ := finalization
    have childAt := childRun 0
    have finalized := finalRun 0
    simp only [Nat.add_zero] at childAt finalized
    obtain ⟨recordedFuel, result, afterCore, recorded⟩ :=
      SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver next graph templates
        metadata uv fragment reached final after (advance seed (bound + 1)) afterPacket admitted.2.2.1
        paddedFits paddedKnown
    obtain ⟨callbackFuel, continued, callbackRun, resources⟩ :=
      eager_program_callback_from_recorded_resources_with_isolated holeKey keyMatches admits formulas solver next graph templates metadata uv
        fragment reached final after checkEmpty edgesOf stop order recursiveDepth recursive
        (advance seed (bound + 1)) (ceiling + bound) afterPacket admitted.2.2.1 paddedFits paddedKnown
        selectionMembers selectionLength actualMass reserved.2 valid marked afterSlots recordedFuel result afterCore recorded
    let folded : Fold := match continued with
      | .complete outputs actual queries =>
          .complete [.complete fragment reached final.query after] outputs actual queries
      | .stopped outputs reason endpoint =>
          .stopped [] outputs (.continuation (.complete fragment reached final.query after) reason endpoint)
    have localOutputs : ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted continued,
        programOutputRolesWithIsolatedExcept valid marked caller before uv output := by
      intro output member
      obtain ⟨roles, markers⟩ := resources.2 output member
      refine ⟨roles, ?_⟩
      intro held heldHandle heldValue different isolated decoded boundary
      have boundedScs : ∀ sc ∈ scs, sc.var < before.core.counter :=
        ready.safe.1.values _ (List.mem_of_getElem? stored)
      have avoids : Avoids before.core.representatives held scs :=
        isolated.incoming _ (List.mem_of_getElem? stored)
      have middleIsolated := SourcePruningEnumerationSharedChildIsolation.observed_isolated_pending
        checkEmpty headFuel headFuel headFuel headFuel headFuel scs value caller reached before middle
        memos.query final.query fragment middle.core outer waiting held heldHandle ready.safe isolated
        boundedScs avoids childAt
      have afterIsolated := middleIsolated.through_finalize reached.checked.native.machine.heap
        headFuel uv held heldHandle fragment middle after (Ne.symm different) finalized
      have reachedLookup := SourcePruningEnumerationNodes.lookupNode_keeps
        caller.checked.native.machine.heap reached.checked.native.machine.heap headPost.effects.keeps
        heldHandle heldValue decoded
      exact markers held heldHandle heldValue afterIsolated reachedLookup boundary
    have fullResources : OutcomeResourcesWithOutputs
        (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (eagerFinal recursiveDepth (advance seed (bound + 1)) (ceiling + bound)) continued :=
      ⟨(resources_outputs_post headPost resources).1, localOutputs⟩
    have finished : OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed)
        (finish uv folded) := by
      cases continued <;>
        simpa only [folded, finish, SourcePruningEnumerationSharedPreparedRecursive.endpoint,
          OutcomeResourcesWithOutputs, OutcomeResources, fallbackPlan,
          SourcePruningEnumerationSharedPreparedRecursive.emitted] using fullResources
    refine ⟨headFuel + callbackFuel, .complete fragment reached final.query after, folded, ?_, ?_, finished⟩
    · intro extra
      have actual := headRun (callbackFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callbackRun (headFuel + extra)
      have common : callbackFuel + (headFuel + extra) = headFuel + callbackFuel + extra := by omega
      rw [common] at actual
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual]
      cases continued <;> rfl
  · obtain ⟨after, outer, waiting, rfl, _counter, _mass⟩ := stopped
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRolesWithIsolatedExcept valid marked caller before uv)
        formulas solver caller (advance seed (bound + 1)) (.complete [] reached final.query) := by
      refine ⟨?_, fun _ member => by cases member⟩
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    refine ⟨headFuel, .stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after),
      .complete [.stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after)] [] reached final.query,
      headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · simpa only [finish, fallbackPlan] using resources_outputs_mono growth.1 growth.2 resources
  · subst receipt
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRolesWithIsolatedExcept valid marked caller before uv)
        formulas solver caller (advance seed (bound + 1)) (.complete [] reached final.query) := by
      refine ⟨?_, fun _ member => by cases member⟩
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    have endpoints : (caller, memos.query) = (reached, final.query) := by
      exact Option.some.inj _advanced
    obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
    refine ⟨headFuel, .rejected caller memos.query before,
      .complete [.rejected caller memos.query before] [] caller memos.query, headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · have fullResources := resources_outputs_mono growth.1 growth.2 resources
      simpa only [finish, fallbackPlan, callerSame, querySame] using fullResources

end ActualProgramOpaqueResources

section ActualProgramCapturedResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_captured_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome) := by
  classical
  let literal : String → Symbol := SourceSynthesisLabelProgramBuildRoles.literal
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
    OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
      (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
    limit (bound + own) ceiling continuation growth seed
  have planFits := fits.mono planGrowth.1
  have planKnown : Heap
      (fun guard => guard ∈ (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed).1)
      caller.checked.native.machine.heap := by
    intro key edge found
    exact planGrowth.2 (known key edge found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        let outcome : Fold := .stopped [] [] (.edge (some .unhandled) (caller, memos.query))
        refine ⟨0, outcome, ?_, ?_⟩
        · intro extra
          rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
          simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
            SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
          rfl
        · constructor
          · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, .inr rfl, ?_⟩
            intro output member
            cases member
          · intro output member
            cases member
    | some projectedFields =>
        rcases projectedFields with ⟨tries, residual⟩
        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, lower, reducing⟩ :=
          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
        obtain ⟨_prepared, middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, middleProtects⟩ := ownReceipt
        have ownAvoids : ∀ held, marked held → Avoids before.core.representatives held scs := by
          intro held tagged
          exact slots.incoming held tagged (.unenumerated (some handle) scs) (List.mem_of_getElem? stored)
        have observed := middleRun
        simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, Option.map_eq_some_iff] at observed
        obtain ⟨allocation, ownRun, endpoints⟩ := observed
        have sameMiddle : allocation.2 = middle := (Prod.mk.inj (List.cons.inj endpoints).1).2
        have ownObserved : SourcePruningEnumerationCachedOwn.suspendMany caller.checked.native.machine.heap tries before =
            some (allocation.1, middle) := by
          rw [← sameMiddle]
          exact ownRun
        obtain ⟨_ownSame, _cacheSame, _ownRaw, _counter, _forest, _safe, middleSlots,
            _oldProtection, _fresh⟩ :=
          SourceSynthesisProgramRolesClassAllocation.suspendMany_program_slots valid literal
            caller.checked.native.machine.heap tries before middle allocation.1 marked packet.safe slots ownObserved
        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
        have inputAvoids : ∀ held, marked held → ∀ value bucket, (value, bucket) ∈ inputs →
            Avoids middle.core.representatives held bucket := by
          intro held tagged value bucket member
          exact (middleProtects held (slots.bounded held tagged) (slots.roots held tagged)
            (ownAvoids held tagged)).2 value bucket member
        have edgeBounds := (shapes parentEntry rows depth free available).2 edge selected
        have triesBound := edgeBounds.2 tries residual projected
        have inputLength : inputs.length ≤ limit := by
          simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using edgeBounds.1
        have inputFacts : ∀ value bucket, (value, bucket) ∈ inputs →
            Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
              bucket.length ≤ bound + own ∧ (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value bucket member
          obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine value bucket member
          have childRank := lower value bucket member
          obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
          cases same
          have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
          have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
            (suspendedVars before.core.counter tries)
          rw [SourcePruningEnumerationCostBounds.suspended_length] at added
          refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
            ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, by omega, ?_, childBounded, childPending⟩
          simp only [List.length_append]
          omega
        have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling := by
          rw [middleMass]
          exact mass
        let yes : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
          fun work fragments reached saved after =>
            let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
            let middle := SelectedEdge.finish residual fragment after
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.complete fragment reached saved finished))
            | none => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.finalizeStopped fragment reached saved middle))
        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
          fun work completed observation candidate =>
            SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
              (some (.stopped completed observation candidate))
        have completedConsumer : ∀ fragments reached saved after,
            TupleInputs formulas solver caller metadata middle inputs fragments reached saved after →
            (marked uv → SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked
              (.node edge.entry.key.symbol fragments)) →
            ∀ current retained, Fits current.2 reached.checked →
              Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
              SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
              ∃ fuel outcome, (∀ extra, yes (fuel + extra) fragments reached saved after = outcome) ∧
                OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver reached
                  (continuation retained current) (finish uv outcome) := by
          intro fragments reached saved after history parentRoles current retained fitted supported afterMass accepted
          let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
          let childAfter := SelectedEdge.finish residual fragment after
          have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
            middleCore middleCounter middleProtects fragments reached saved after history
          have dataSlots := child_inputs_program_slots valid literal marked formulas solver caller reached metadata
            before childAfter scs fragment saved packet.safe slots ownAvoids data
          by_cases chosen : marked uv
          · obtain ⟨next, final, finalFuel, finished, callbackFuel, result, afterCore, finalReceipt, callback,
                _fragmentRoles, finalSlots, _callbackSlots, _coupled⟩ :=
              finalized_program_callback_observation valid marked formulas solver caller reached metadata before childAfter
                uv handle scs fragment saved ready stored incoming chosen ⟨data, dataSlots, parentRoles chosen⟩
                graph templates current fitted supported
            obtain ⟨_post, querySame, finalAt, finishedPacket, fragmentBound, _core, finalMass, _stored, _root⟩ := finalReceipt
            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass afterMass
            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
              eager_program_callback_from_recorded_resources holeKey keyMatches admits formulas solver next graph templates
                metadata uv fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current
                retained finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
                valid marked finalSlots callbackFuel result afterCore callback
            rw [querySame] at hookAt
            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
            let outcome : Fold := match (generalizing := false) hookOutcome with
              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
            · intro extra
              have finalizeAt := finalAt (hookFuel + extra)
              rw [← Nat.add_assoc] at finalizeAt
              have continued := hookAt (finalFuel + extra)
              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
              rw [same] at continued
              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
                (finalFuel + hookFuel + extra) uv fragment childAfter with
                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.complete fragment reached saved finished))
                | none => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
              rw [finalizeAt]
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
                simpa only [hook] using continued
              rw [hookStep]
              cases hookOutcome <;> rfl
            · cases hookOutcome <;> exact resources
          · obtain ⟨next, final, finalFuel, finished, callbackFuel, result, afterCore, finalReceipt, callback,
                finalSlots, _callbackSlots, _coupled⟩ :=
              finalized_unmarked_callback_observation valid marked formulas solver caller reached metadata before childAfter
                uv handle scs fragment saved ready stored incoming chosen slots data graph templates current fitted supported
            obtain ⟨_post, querySame, finalAt, finishedPacket, fragmentBound, _core, finalMass, _stored, _root⟩ := finalReceipt
            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass afterMass
            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
              eager_program_callback_from_recorded_resources holeKey keyMatches admits formulas solver next graph templates
                metadata uv fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current
                retained finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
                valid marked finalSlots callbackFuel result afterCore callback
            rw [querySame] at hookAt
            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
            let outcome : Fold := match (generalizing := false) hookOutcome with
              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
            · intro extra
              have finalizeAt := finalAt (hookFuel + extra)
              rw [← Nat.add_assoc] at finalizeAt
              have continued := hookAt (finalFuel + extra)
              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
              rw [same] at continued
              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
                (finalFuel + hookFuel + extra) uv fragment childAfter with
                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.complete fragment reached saved finished))
                | none => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
              rw [finalizeAt]
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
                simpa only [hook] using continued
              rw [hookStep]
              cases hookOutcome <;> rfl
            · cases hookOutcome <;> exact resources
        have tupleComplete : ∃ fuel outcome,
            (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              (yes (fuel + extra)) (no (fuel + extra)) inputs caller middle memos.query = outcome) ∧
            OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
              (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome) := by
          by_cases chosen : marked uv
          · have edgeFields := fields chosen
            obtain ⟨payload, present, role⟩ := slots.stored uv chosen
            have same : payload = .unenumerated (some handle) scs := Option.some.inj (present.symm.trans stored)
            subst payload
            have bucketScope : EnumerationSemantics.ValidSuspended scs ∧
                SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs := by
              cases role with
              | pending _native _bucket _original _found _valueFields validTries annotationPaths =>
                  exact ⟨validTries, annotationPaths⟩
            let programIndex : Nat → Prop := fun index =>
              (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
                (edge.entry.key.symbol = literal "filter" ∧ index = 1)
            have inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
                ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
              intro sc member
              refine ⟨bucketScope.1 sc member, ?_⟩
              intro path represented
              obtain ⟨tail, same⟩ := bucketScope.2 sc member path represented
              exact ⟨tail, same.symm⟩
            have inputFields : ∀ index value bucket, inputs[index]? = some (value, bucket) → programIndex index →
                SourceSynthesisHereditaryProgramFields.ValueFields valid literal value ∧
                  EnumerationSemantics.ValidSuspended bucket ∧
                  SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket := by
              intro index value bucket selectedInput wanted
              obtain ⟨childFields, _inheritedEmpty, _ownBucket, childScope⟩ :=
                SourceSynthesisProgramChildScope.program_child_scope valid edge edgeFields scs before.core.counter
                  inherited tries residual projected index value bucket selectedInput wanted
              refine ⟨childFields, fun sc member => (childScope sc member).1, ?_⟩
              intro sc member path represented
              obtain ⟨tail, same⟩ := (childScope sc member).2 path represented
              exact ⟨tail, same.symm⟩
            have tupleConsumers : ProgramTupleConsumersWithOutputs (programOutputRoles valid marked) valid literal marked programIndex
                formulas solver caller metadata middle inputs uv continuation admitted yes no := by
              constructor
              · intro fragments reached saved after history current retained fitted supported afterMass accepted
                obtain ⟨history, _afterSlots, countSame, childRoles⟩ := history
                have fragmentCount : fragments.length = edge.children.length := by
                  simpa only [inputs, SourcePruningEnumerationEdgeInputs.children,
                    List.length_map, List.length_zipIdx] using countSame
                have assembled := SourceSynthesisProgramParentCallbackRoles.fragment_roles_of_children valid marked edge
                  edgeFields fragments fragmentCount childRoles
                exact completedConsumer fragments reached saved after history (fun _ => assembled)
                  current retained fitted supported afterMass accepted
              · intro completed reached saved after outer waiting next final post query _prefixRoles current retained fitted supported _accepted
                let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
                  ((.ok (some []), reached, saved, outer, waiting)) (some after)
                let outcome : Fold := .complete [receipt] [] reached saved
                have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver reached current (finish uv outcome) := by
                  constructor
                  · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                    intro output member
                    cases member
                  · intro output member
                    cases member
                have enlarged := growth retained current
                exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
            have child := eager_program_child_height_complete_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver
            have tuple := eager_program_tuple_complete_of_child_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver child limit
            exact tuple valid marked programIndex inventory caller memos metadata middle seed
              (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
              inputFacts middleSlots inputAvoids inputFields shapes selectionMembers selectionLength reserved growth tupleConsumers
          · have tupleConsumers : TupleConsumersWithOutputs (programOutputRoles valid marked) formulas solver caller metadata middle inputs uv continuation admitted yes no := by
              constructor
              · intro fragments reached saved after history current retained fitted supported afterMass accepted
                exact completedConsumer fragments reached saved after history (fun impossible => (chosen impossible).elim)
                  current retained fitted supported afterMass accepted
              · intro completed reached saved after outer waiting next final post query current retained fitted supported _accepted
                let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
                  ((.ok (some []), reached, saved, outer, waiting)) (some after)
                let outcome : Fold := .complete [receipt] [] reached saved
                have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver reached current (finish uv outcome) := by
                  constructor
                  · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                    intro output member
                    cases member
                  · intro output member
                    cases member
                have enlarged := growth retained current
                exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
            have child := eager_child_height_complete_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver
            have tuple := eager_tuple_complete_of_child_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver child limit
            exact tuple inventory caller memos metadata middle seed
              (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
              inputFacts shapes selectionMembers selectionLength reserved growth tupleConsumers
        obtain ⟨fuel, outcome, running, resources⟩ := tupleComplete
        refine ⟨fuel, outcome, ?_, resources⟩
        intro extra
        rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts, reducing]
        exact running extra
  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
    refine ⟨0, outcome, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
        SourcePruningEnumerationCachedOwn.prepare, allowed]
      rfl
    · constructor
      · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
        intro output member
        cases member
      · intro output member
        cases member

-- The captured edge retains roles and isolated markers at other slots.
private theorem eager_program_captured_resources_with_isolated_except
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeWithIsolatedComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome) := by
  classical
  let literal : String → Symbol := SourceSynthesisLabelProgramBuildRoles.literal
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
    OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
      (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
    limit (bound + own) ceiling continuation growth seed
  have planFits := fits.mono planGrowth.1
  have planKnown : Heap
      (fun guard => guard ∈ (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed).1)
      caller.checked.native.machine.heap := by
    intro key edge found
    exact planGrowth.2 (known key edge found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        let outcome : Fold := .stopped [] [] (.edge (some .unhandled) (caller, memos.query))
        refine ⟨0, outcome, ?_, ?_⟩
        · intro extra
          rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
          simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
            SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
          rfl
        · constructor
          · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, .inr rfl, ?_⟩
            intro output member
            cases member
          · intro output member
            cases member
    | some projectedFields =>
        rcases projectedFields with ⟨tries, residual⟩
        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, lower, reducing⟩ :=
          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
        obtain ⟨_prepared, middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, middleProtects⟩ := ownReceipt
        have ownAvoids : ∀ held, marked held → Avoids before.core.representatives held scs := by
          intro held tagged
          exact slots.incoming held tagged (.unenumerated (some handle) scs) (List.mem_of_getElem? stored)
        have observed := middleRun
        simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, Option.map_eq_some_iff] at observed
        obtain ⟨allocation, ownRun, endpoints⟩ := observed
        have sameMiddle : allocation.2 = middle := (Prod.mk.inj (List.cons.inj endpoints).1).2
        have ownObserved : SourcePruningEnumerationCachedOwn.suspendMany caller.checked.native.machine.heap tries before =
            some (allocation.1, middle) := by
          rw [← sameMiddle]
          exact ownRun
        obtain ⟨_ownSame, _cacheSame, _ownRaw, _counter, _forest, _safe, middleSlots,
            _oldProtection, _fresh⟩ :=
          SourceSynthesisProgramRolesClassAllocation.suspendMany_program_slots valid literal
            caller.checked.native.machine.heap tries before middle allocation.1 marked packet.safe slots ownObserved
        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
        have inputAvoids : ∀ held, marked held → ∀ value bucket, (value, bucket) ∈ inputs →
            Avoids middle.core.representatives held bucket := by
          intro held tagged value bucket member
          exact (middleProtects held (slots.bounded held tagged) (slots.roots held tagged)
            (ownAvoids held tagged)).2 value bucket member
        have edgeBounds := (shapes parentEntry rows depth free available).2 edge selected
        have triesBound := edgeBounds.2 tries residual projected
        have inputLength : inputs.length ≤ limit := by
          simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using edgeBounds.1
        have inputFacts : ∀ value bucket, (value, bucket) ∈ inputs →
            Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
              bucket.length ≤ bound + own ∧ (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value bucket member
          obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine value bucket member
          have childRank := lower value bucket member
          obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
          cases same
          have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
          have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
            (suspendedVars before.core.counter tries)
          rw [SourcePruningEnumerationCostBounds.suspended_length] at added
          refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
            ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, by omega, ?_, childBounded, childPending⟩
          simp only [List.length_append]
          omega
        have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling := by
          rw [middleMass]
          exact mass
        let yes : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
          fun work fragments reached saved after =>
            let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
            let middle := SelectedEdge.finish residual fragment after
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.complete fragment reached saved finished))
            | none => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.finalizeStopped fragment reached saved middle))
        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
          fun work completed observation candidate =>
            SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
              (some (.stopped completed observation candidate))
        have completedConsumer : ∀ fragments reached saved after,
            TupleInputs formulas solver caller metadata middle inputs fragments reached saved after →
            (marked uv → SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked
              (.node edge.entry.key.symbol fragments)) →
            ∀ current retained, Fits current.2 reached.checked →
              Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
              SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
              ∃ fuel outcome, (∀ extra, yes (fuel + extra) fragments reached saved after = outcome) ∧
                OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver reached
                  (continuation retained current) (finish uv outcome) := by
          intro fragments reached saved after history parentRoles current retained fitted supported afterMass accepted
          let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
          let childAfter := SelectedEdge.finish residual fragment after
          have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
            middleCore middleCounter middleProtects fragments reached saved after history
          have dataSlots := child_inputs_program_slots valid literal marked formulas solver caller reached metadata
            before childAfter scs fragment saved packet.safe slots ownAvoids data
          by_cases chosen : marked uv
          · obtain ⟨next, final, finalFuel, finished, callbackFuel, result, afterCore, finalReceipt, callback,
                _fragmentRoles, finalSlots, _callbackSlots, _coupled⟩ :=
              finalized_program_callback_observation valid marked formulas solver caller reached metadata before childAfter
                uv handle scs fragment saved ready stored incoming chosen ⟨data, dataSlots, parentRoles chosen⟩
                graph templates current fitted supported
            obtain ⟨childPost, querySame, finalAt, finishedPacket, fragmentBound, _core, finalMass, _stored, _root⟩ := finalReceipt
            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass afterMass
            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
              eager_program_callback_from_recorded_resources_with_isolated holeKey keyMatches admits formulas solver next graph templates
                metadata uv fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current
                retained finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
                valid marked finalSlots callbackFuel result afterCore callback
            have localOutputs :
                ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted hookOutcome,
                  programOutputRolesWithIsolatedExcept valid marked caller before uv output := by
              intro output member
              obtain ⟨roles, markers⟩ := resources.2 output member
              refine ⟨roles, ?_⟩
              intro held heldHandle heldValue different isolated decoded boundary
              have avoids : Avoids before.core.representatives held scs :=
                isolated.incoming _ (List.mem_of_getElem? stored)
              have finalized := finalAt 0
              simp only [Nat.add_zero] at finalized
              obtain ⟨_, retained⟩ := finalized_child_inputs_isolated_pending
                formulas solver caller reached metadata before childAfter finished scs fragment saved
                uv held heldHandle finalFuel packet.safe isolated avoids data
                (Ne.symm different) finalized
              have reachedLookup := SourcePruningEnumerationNodes.lookupNode_keeps
                caller.checked.native.machine.heap reached.checked.native.machine.heap
                childPost.effects.keeps heldHandle heldValue decoded
              exact markers held heldHandle heldValue retained reachedLookup boundary
            have resources : OutcomeResourcesWithOutputs
                (programOutputRolesWithIsolatedExcept valid marked caller before uv)
                formulas solver reached (continuation retained current) hookOutcome :=
              ⟨resources.1, localOutputs⟩
            rw [querySame] at hookAt
            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
            let outcome : Fold := match (generalizing := false) hookOutcome with
              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
            · intro extra
              have finalizeAt := finalAt (hookFuel + extra)
              rw [← Nat.add_assoc] at finalizeAt
              have continued := hookAt (finalFuel + extra)
              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
              rw [same] at continued
              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
                (finalFuel + hookFuel + extra) uv fragment childAfter with
                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.complete fragment reached saved finished))
                | none => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
              rw [finalizeAt]
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
                simpa only [hook] using continued
              rw [hookStep]
              cases hookOutcome <;> rfl
            · cases hookOutcome <;> exact resources
          · obtain ⟨next, final, finalFuel, finished, callbackFuel, result, afterCore, finalReceipt, callback,
                finalSlots, _callbackSlots, _coupled⟩ :=
              finalized_unmarked_callback_observation valid marked formulas solver caller reached metadata before childAfter
                uv handle scs fragment saved ready stored incoming chosen slots data graph templates current fitted supported
            obtain ⟨childPost, querySame, finalAt, finishedPacket, fragmentBound, _core, finalMass, _stored, _root⟩ := finalReceipt
            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass afterMass
            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
              eager_program_callback_from_recorded_resources_with_isolated holeKey keyMatches admits formulas solver next graph templates
                metadata uv fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current
                retained finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
                valid marked finalSlots callbackFuel result afterCore callback
            have localOutputs :
                ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted hookOutcome,
                  programOutputRolesWithIsolatedExcept valid marked caller before uv output := by
              intro output member
              obtain ⟨roles, markers⟩ := resources.2 output member
              refine ⟨roles, ?_⟩
              intro held heldHandle heldValue different isolated decoded boundary
              have avoids : Avoids before.core.representatives held scs :=
                isolated.incoming _ (List.mem_of_getElem? stored)
              have finalized := finalAt 0
              simp only [Nat.add_zero] at finalized
              obtain ⟨_, retained⟩ := finalized_child_inputs_isolated_pending
                formulas solver caller reached metadata before childAfter finished scs fragment saved
                uv held heldHandle finalFuel packet.safe isolated avoids data
                (Ne.symm different) finalized
              have reachedLookup := SourcePruningEnumerationNodes.lookupNode_keeps
                caller.checked.native.machine.heap reached.checked.native.machine.heap
                childPost.effects.keeps heldHandle heldValue decoded
              exact markers held heldHandle heldValue retained reachedLookup boundary
            have resources : OutcomeResourcesWithOutputs
                (programOutputRolesWithIsolatedExcept valid marked caller before uv)
                formulas solver reached (continuation retained current) hookOutcome :=
              ⟨resources.1, localOutputs⟩
            rw [querySame] at hookAt
            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
            let outcome : Fold := match (generalizing := false) hookOutcome with
              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
            · intro extra
              have finalizeAt := finalAt (hookFuel + extra)
              rw [← Nat.add_assoc] at finalizeAt
              have continued := hookAt (finalFuel + extra)
              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
              rw [same] at continued
              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
                (finalFuel + hookFuel + extra) uv fragment childAfter with
                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.complete fragment reached saved finished))
                | none => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
              rw [finalizeAt]
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
                simpa only [hook] using continued
              rw [hookStep]
              cases hookOutcome <;> rfl
            · cases hookOutcome <;> exact resources
        have tupleComplete : ∃ fuel outcome,
            (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              (yes (fuel + extra)) (no (fuel + extra)) inputs caller middle memos.query = outcome) ∧
            OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
              (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome) := by
          by_cases chosen : marked uv
          · have edgeFields := fields chosen
            obtain ⟨payload, present, role⟩ := slots.stored uv chosen
            have same : payload = .unenumerated (some handle) scs := Option.some.inj (present.symm.trans stored)
            subst payload
            have bucketScope : EnumerationSemantics.ValidSuspended scs ∧
                SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs := by
              cases role with
              | pending _native _bucket _original _found _valueFields validTries annotationPaths =>
                  exact ⟨validTries, annotationPaths⟩
            let programIndex : Nat → Prop := fun index =>
              (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
                (edge.entry.key.symbol = literal "filter" ∧ index = 1)
            have inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
                ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
              intro sc member
              refine ⟨bucketScope.1 sc member, ?_⟩
              intro path represented
              obtain ⟨tail, same⟩ := bucketScope.2 sc member path represented
              exact ⟨tail, same.symm⟩
            have inputFields : ∀ index value bucket, inputs[index]? = some (value, bucket) → programIndex index →
                SourceSynthesisHereditaryProgramFields.ValueFields valid literal value ∧
                  EnumerationSemantics.ValidSuspended bucket ∧
                  SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket := by
              intro index value bucket selectedInput wanted
              obtain ⟨childFields, _inheritedEmpty, _ownBucket, childScope⟩ :=
                SourceSynthesisProgramChildScope.program_child_scope valid edge edgeFields scs before.core.counter
                  inherited tries residual projected index value bucket selectedInput wanted
              refine ⟨childFields, fun sc member => (childScope sc member).1, ?_⟩
              intro sc member path represented
              obtain ⟨tail, same⟩ := (childScope sc member).2 path represented
              exact ⟨tail, same.symm⟩
            have tupleConsumers : ProgramTupleConsumersWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) valid literal marked programIndex
                formulas solver caller metadata middle inputs uv continuation admitted yes no := by
              constructor
              · intro fragments reached saved after history current retained fitted supported afterMass accepted
                obtain ⟨history, _afterSlots, countSame, childRoles⟩ := history
                have fragmentCount : fragments.length = edge.children.length := by
                  simpa only [inputs, SourcePruningEnumerationEdgeInputs.children,
                    List.length_map, List.length_zipIdx] using countSame
                have assembled := SourceSynthesisProgramParentCallbackRoles.fragment_roles_of_children valid marked edge
                  edgeFields fragments fragmentCount childRoles
                exact completedConsumer fragments reached saved after history (fun _ => assembled)
                  current retained fitted supported afterMass accepted
              · intro completed reached saved after outer waiting next final post query _prefixRoles current retained fitted supported _accepted
                let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
                  ((.ok (some []), reached, saved, outer, waiting)) (some after)
                let outcome : Fold := .complete [receipt] [] reached saved
                have resources : OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver reached current (finish uv outcome) := by
                  constructor
                  · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                    intro output member
                    cases member
                  · intro output member
                    cases member
                have enlarged := growth retained current
                exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
            have child := eager_program_child_height_complete_with_outputs (programOutputRolesWithIsolatedExcept valid marked caller before uv)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver
            have tuple := eager_program_tuple_complete_of_child_with_outputs (programOutputRolesWithIsolatedExcept valid marked caller before uv)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver child limit
            exact tuple valid marked programIndex inventory caller memos metadata middle seed
              (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
              inputFacts middleSlots inputAvoids inputFields shapes selectionMembers selectionLength reserved growth tupleConsumers
          · have tupleConsumers : TupleConsumersWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller metadata middle inputs uv continuation admitted yes no := by
              constructor
              · intro fragments reached saved after history current retained fitted supported afterMass accepted
                exact completedConsumer fragments reached saved after history (fun impossible => (chosen impossible).elim)
                  current retained fitted supported afterMass accepted
              · intro completed reached saved after outer waiting next final post query current retained fitted supported _accepted
                let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
                  ((.ok (some []), reached, saved, outer, waiting)) (some after)
                let outcome : Fold := .complete [receipt] [] reached saved
                have resources : OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver reached current (finish uv outcome) := by
                  constructor
                  · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                    intro output member
                    cases member
                  · intro output member
                    cases member
                have enlarged := growth retained current
                exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
            have child := eager_child_height_complete_with_outputs (programOutputRolesWithIsolatedExcept valid marked caller before uv)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver
            have tuple := eager_tuple_complete_of_child_with_outputs (programOutputRolesWithIsolatedExcept valid marked caller before uv)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver child limit
            exact tuple inventory caller memos metadata middle seed
              (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
              inputFacts shapes selectionMembers selectionLength reserved growth tupleConsumers
        obtain ⟨fuel, outcome, running, resources⟩ := tupleComplete
        refine ⟨fuel, outcome, ?_, resources⟩
        intro extra
        rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts, reducing]
        exact running extra
  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
    refine ⟨0, outcome, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
        SourcePruningEnumerationCachedOwn.prepare, allowed]
      rfl
    · constructor
      · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
        intro output member
        cases member
      · intro output member
        cases member
end ActualProgramCapturedResources

section ActualProgramCapturedRowsResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)

private theorem eager_program_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat)
    (valid : Constraint → Prop) (marked : Nat → Prop) :
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
    Packet formulas solver inventory caller memos metadata before →
    EnumerationDriver.Ready uv before.core →
    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv before.core →
    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (marked uv → ∀ edge ∈ alternatives, SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained)
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
            graph templates stop order (fuel + extra) metadata uv)
          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome) := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet _ready _stored _incoming fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending _slots
        alternatives length _selected _fields _shapes _selectionMembers _selectionLength _reserved
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          constructor
          · exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
          · intro output member
            cases member
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending slots
        alternatives length selected fields shapes selectionMembers selectionLength reserved
      let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
      let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
      have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
          current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      cases alternatives with
      | nil =>
          have enlarged := iterate_ge row rowGrowth seed (count + 1)
          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
              caller.checked.native.machine.heap := by
            intro key edge found
            exact enlarged.2 (known key edge found)
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          constructor
          · exact ⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
              supported, rfl, rfl, fun _ member => by cases member⟩
          · intro output member
            cases member
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_program_captured_resources
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
            captured limit own height inventory caller memos metadata before seed bound ceiling scs uv handle
            packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked
            edge (selected edge (by simp)) bounded pending shapes selectionMembers selectionLength firstReserved
            valid marked slots (fun tagged => fields tagged edge (by simp))
          have farther := iterate_ge row rowGrowth (row seed) count
          cases headOutcome with
          | stopped processed outputs current =>
              refine ⟨headFuel, .stopped processed outputs current, ?_, resources_outputs_mono farther.1 farther.2 headResources⟩
              intro extra
              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
          | complete processed outputs reached saved =>
              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, _outputResources⟩ :=
                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources.1
              have laterReserved : ∀ index, index < count →
                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
                intro index inside
                exact reserved (index + 1) (by omega)
              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              have reachedSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
                caller.checked.native.machine.heap reached.checked.native.machine.heap before.core marked post.effects.keeps slots
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
                bound ceiling scs uv handle reachedPacket ready stored incoming reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending reachedSlots
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member))
                (fun tagged edge member => fields tagged edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved
              let result : Fold := match (generalizing := false) tailOutcome with
                | .complete later remaining finalCaller finalQueries =>
                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
              · intro extra
                have headAt := headRunning (tailFuel + extra)
                have tailAt := tailRunning (headFuel + extra)
                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
                rw [hs] at headAt
                rw [ts, query] at tailAt
                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
                dsimp only
                rw [tailAt]
                cases tailOutcome <;> rfl
              · simpa only [SourcePruningEnumerationFiniteReservation.iterate_succ, row, result] using
                  (resources_outputs_append uv processed outputs tailOutcome post farther.1 farther.2
                    (by simpa only [query, finish, row] using headResources) tailResources)

-- The captured row fold retains the original caller and marker observer.
private theorem eager_program_captured_rows_resources_with_isolated_except
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeWithIsolatedComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat)
    (valid : Constraint → Prop) (marked : Nat → Prop) :
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
    Packet formulas solver inventory caller memos metadata before →
    EnumerationDriver.Ready uv before.core →
    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv before.core →
    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (marked uv → ∀ edge ∈ alternatives, SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained)
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
            graph templates stop order (fuel + extra) metadata uv)
          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome) := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet _ready _stored _incoming fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending _slots
        alternatives length _selected _fields _shapes _selectionMembers _selectionLength _reserved
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          constructor
          · exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
          · intro output member
            cases member
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending slots
        alternatives length selected fields shapes selectionMembers selectionLength reserved
      let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
      let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
      have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
          current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      cases alternatives with
      | nil =>
          have enlarged := iterate_ge row rowGrowth seed (count + 1)
          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
              caller.checked.native.machine.heap := by
            intro key edge found
            exact enlarged.2 (known key edge found)
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          constructor
          · exact ⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
              supported, rfl, rfl, fun _ member => by cases member⟩
          · intro output member
            cases member
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_program_captured_resources_with_isolated_except
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
            captured limit own height inventory caller memos metadata before seed bound ceiling scs uv handle
            packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked
            edge (selected edge (by simp)) bounded pending shapes selectionMembers selectionLength firstReserved
            valid marked slots (fun tagged => fields tagged edge (by simp))
          have farther := iterate_ge row rowGrowth (row seed) count
          cases headOutcome with
          | stopped processed outputs current =>
              refine ⟨headFuel, .stopped processed outputs current, ?_, resources_outputs_mono farther.1 farther.2 headResources⟩
              intro extra
              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
          | complete processed outputs reached saved =>
              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, _outputResources⟩ :=
                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources.1
              have laterReserved : ∀ index, index < count →
                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
                intro index inside
                exact reserved (index + 1) (by omega)
              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              have reachedSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
                caller.checked.native.machine.heap reached.checked.native.machine.heap before.core marked post.effects.keeps slots
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
                bound ceiling scs uv handle reachedPacket ready stored incoming reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending reachedSlots
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member))
                (fun tagged edge member => fields tagged edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved
              have tailOutputs :
                  ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted (finish uv tailOutcome),
                    programOutputRolesWithIsolatedExcept valid marked caller before uv output := by
                intro output member
                obtain ⟨roles, markers⟩ := tailResources.2 output member
                refine ⟨roles, ?_⟩
                intro held heldHandle heldValue different isolated decoded boundary
                have reachedLookup := SourcePruningEnumerationNodes.lookupNode_keeps
                  caller.checked.native.machine.heap reached.checked.native.machine.heap
                  post.effects.keeps heldHandle heldValue decoded
                exact markers held heldHandle heldValue different isolated reachedLookup boundary
              have tailResources : OutcomeResourcesWithOutputs
                  (programOutputRolesWithIsolatedExcept valid marked caller before uv)
                  formulas solver reached (iterate row (row seed) count) (finish uv tailOutcome) :=
                ⟨tailResources.1, tailOutputs⟩
              let result : Fold := match (generalizing := false) tailOutcome with
                | .complete later remaining finalCaller finalQueries =>
                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
              · intro extra
                have headAt := headRunning (tailFuel + extra)
                have tailAt := tailRunning (headFuel + extra)
                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
                rw [hs] at headAt
                rw [ts, query] at tailAt
                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
                dsimp only
                rw [tailAt]
                cases tailOutcome <;> rfl
              · simpa only [SourcePruningEnumerationFiniteReservation.iterate_succ, row, result] using
                  (resources_outputs_append uv processed outputs tailOutcome post farther.1 farther.2
                    (by simpa only [query, finish, row] using headResources) tailResources)
end ActualProgramCapturedRowsResources

section ActualProgramPreparedResources
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate)

private theorem eager_program_prepared_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ ceiling)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
    := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel observed outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
    OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
      (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  obtain ⟨preparationFuel, decoded, value, heap, entered, retained,
    preparedFits, _valueMass, preparedKnown, frame, enteredIncoming, sameMass⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_current
      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 fits incoming
      (fun guard => guard ∈ seed.1) known
  obtain ⟨preparationRun, decodedLookup, preparationPost, enteredPacket, stable, enteredReady,
    enteredStored, _counter, _values, _flags, _waiting, available, closed, _meaning, _satisfaction⟩ := retained
  let preparedCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
  have currentFits : Fits start.2 preparedCaller.checked := preparedFits
  have currentKnown : Heap (fun guard => guard ∈ start.1) preparedCaller.checked.native.machine.heap := preparedKnown
  have currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core ≤ ceiling := by
    rw [sameMass]
    exact mass
  have nativeSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
    caller.checked.native.machine.heap heap before.core marked preparationPost.effects.keeps slots
  have currentSlots := SourcePruningEnumerationSharedPreparedRecursive.render_stable_slots
    heap before.core entered.core valid marked stable nativeSlots
  have markedFields (tagged : marked uv) := SourcePruningEnumerationSharedPreparedRecursive.prepared_marked_fields
    preparationFuel preparationFuel uv handle scs caller before entered decoded value heap valid marked slots stored
    decodedLookup (preparationRun 0) tagged
  by_cases empty : value = .empty
  · subst value
    let folded : Fold := .complete [.rejected preparedCaller memos.query entered] [] preparedCaller memos.query
    have finalGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
    have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv folded) := by
      refine ⟨?_, ?_⟩
      · change OutcomeResources (Typing := Typing) formulas solver caller
          (nodePlan limit own limit ceiling ceiling continuation start) (.complete [] preparedCaller memos.query)
        refine ⟨preparedCaller, inventory, memos, preparationPost, currentFits.mono finalGrowth.1, ?_, rfl, rfl, ?_⟩
        · intro key edge found
          exact finalGrowth.2 (currentKnown key edge found)
        · intro output member
          cases member
      · intro output member
        change output ∈ ([] : List (Output (bits + 2) Typing)) at member
        cases member
    refine ⟨preparationFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done .empty heap)), folded, ?_, resources⟩
    intro extra
    unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
    rw [preparationRun extra]
    cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
      simp only [terminal, Bool.false_eq_true, ↓reduceIte, frame,
        SourcePruningEnumerationSharedSelectedOpaqueDispatch.empty,
        SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, folded, preparedCaller]
  by_cases ordinary : ∃ entry rows depth free,
      value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
  · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
    subst value
    let captured := preparedCaller.checked.native.machine.heap
    obtain ⟨heights, shapes⟩ := SourcePruningEnumerationSharedEagerCapturedBounds.captured_payload_bounds
      start captured enteredPacket.context.ready.semantic.ready.semantic.1.normal.facts.linked
      (SourceCurrentConstrainedCapRequiredResources.of_checked currentFits) currentKnown
    have nodeHeight := heights (.node entry rows depth free) available
    have positive : 0 < limit := by
      change MergedOrdinaryHeight.edgesHeight rows + 1 ≤ limit at nodeHeight
      omega
    let height := limit - 1
    have heightSame : height + 1 = limit := by dsimp only [height]; omega
    have ranked : MergedOrdinaryHeight.height (.node entry rows depth free) ≤ height + 1 := by
      rw [heightSame]
      exact nodeHeight
    have computed : nodeReserved bits limit own (height + 1) ceiling ceiling continuation admitted start := by
      rw [heightSame]
      exact planned
    unfold nodeReserved at computed
    let first := fallbackPlan ceiling ceiling continuation start
    let row := fun current => tuplePlan (nodePlan limit own height) limit (ceiling + own) ceiling continuation current
    have firstGrowth := fallbackPlan_ge ceiling ceiling continuation growth start
    have firstKnown : Heap (fun guard => guard ∈ first.1) preparedCaller.checked.native.machine.heap := by
      intro key edge found
      exact firstGrowth.2 (currentKnown key edge found)
    have rowReserved : ∀ index, index < limit →
        tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
          limit (ceiling + own) ceiling continuation admitted (iterate row first index) := computed.2
    have length : (edgesOf (.node entry rows depth free)).length ≤ limit :=
      Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
    have bounded : ∀ sc ∈ scs, sc.var < entered.core.counter :=
      enteredReady.safe.1.values _ (List.mem_of_getElem? enteredStored)
    have pending := EnumerationReferences.pending_inputs entered.core enteredPacket.pending uv (some handle) scs enteredStored
    have rowFields : marked uv → ∀ edge ∈ edgesOf (.node entry rows depth free),
        SourceSynthesisHereditaryProgramFields.EdgeFields valid SourceSynthesisLabelProgramBuildRoles.literal edge := by
      intro tagged edge member
      have actualFields := (markedFields tagged).1
      cases actualFields with
      | node _ _ _ _ checked => exact checked edge (selectionMembers entry rows depth free edge member)
    obtain ⟨branchFuel, outcome, branchRun, certificate⟩ := eager_program_captured_rows_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      captured limit own height limit valid marked inventory preparedCaller memos metadata entered first ceiling ceiling scs uv handle
      enteredPacket enteredReady enteredStored enteredIncoming (currentFits.mono firstGrowth.1) firstKnown
      (SourceEqualityRequiredCache.pure_keeps captured enteredPacket.context.ready.semantic.ready)
      currentMass bucketBound entry rows depth free available closed ranked bounded pending currentSlots
      (edgesOf (.node entry rows depth free)) length (selectionMembers entry rows depth free) rowFields shapes
      selectionMembers selectionLength rowReserved
    have finalSame : eagerFinal (recursiveDepth + 1) seed ceiling = iterate row first limit := by
      change nodePlan limit own limit ceiling ceiling continuation start = _
      calc
        nodePlan limit own limit ceiling ceiling continuation start =
            nodePlan limit own (height + 1) ceiling ceiling continuation start :=
          congrArg (fun h => nodePlan limit own h ceiling ceiling continuation start) heightSame.symm
        _ = iterate row first limit := by
          unfold nodePlan
          rfl
    have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) := by
      rw [finalSame]
      exact resources_outputs_post preparationPost certificate
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done (.node entry rows depth free) heap)),
      outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have atBranch := branchRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at atBranch
    unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
    rw [atPreparation]
    simp only [nonterminal, Bool.false_eq_true, ↓reduceIte]
    rw [frame, atBranch]
  · have dispatch : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false := by
      cases value with
      | node entry rows depth free =>
          cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
          | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
          | true => rfl
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ => rfl
    have unmarked : ¬marked uv := by
      intro tagged
      have currentFields := markedFields tagged
      have fields := currentFields.1
      cases fields with
      | empty => exact empty rfl
      | node entry rows depth free _checked =>
          exact ordinary ⟨entry, rows, depth, free, rfl,
            eager_program_annotation_nonterminal scs currentFields.2.2⟩
    obtain ⟨branchFuel, receipt, outcome, rawRun, receiptRun, certificate⟩ := eager_program_opaque_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      inventory preparedCaller memos metadata entered start ceiling ceiling uv handle scs value enteredPacket enteredReady
      enteredStored enteredIncoming available closed dispatch currentFits currentKnown currentMass bucketBound
      selectionMembers selectionLength (nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned)
      valid marked currentSlots unmarked
    have enlarged := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
    have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) :=
      resources_outputs_post preparationPost (resources_outputs_mono enlarged.1 enlarged.2 certificate)
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)), outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have rawAt := rawRun (preparationFuel + extra)
    have continued := receiptRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at rawAt continued
    have composed : SourcePruningEnumerationSharedReceiptContinuation.run
        (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query) = outcome := by
      rw [rawAt]
      exact continued
    have actual : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) edgesOf)
        (hook (preparationFuel + branchFuel + extra)) checkEmpty
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) uv edgesOf caller before memos.query =
      (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)),
        some (SourcePruningEnumerationSharedReceiptContinuation.run
          (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
          (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query))) := by
      unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      rw [atPreparation]
      cases value with
      | node entry rows depth free =>
          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, here⟩).elim
            | true => rfl
          simp only [terminal, ↓reduceIte, frame, preparedCaller]
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
            simp only [here, Bool.false_eq_true, ↓reduceIte, frame, preparedCaller]
    rw [composed] at actual
    exact actual

-- Preparation retains the original marker observer through its reached cache and heap.
private theorem eager_program_prepared_resources_with_isolated_except
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeWithIsolatedComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ ceiling)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
      OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
    := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel observed outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
    OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
      (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  obtain ⟨preparationFuel, decoded, value, heap, entered, retained,
    preparedFits, _valueMass, preparedKnown, frame, enteredIncoming, sameMass⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_current
      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 fits incoming
      (fun guard => guard ∈ seed.1) known
  obtain ⟨preparationRun, decodedLookup, preparationPost, enteredPacket, stable, enteredReady,
    enteredStored, _counter, _values, _flags, _waiting, available, closed, _meaning, _satisfaction⟩ := retained
  let preparedCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
  have currentFits : Fits start.2 preparedCaller.checked := preparedFits
  have currentKnown : Heap (fun guard => guard ∈ start.1) preparedCaller.checked.native.machine.heap := preparedKnown
  have currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core ≤ ceiling := by
    rw [sameMass]
    exact mass
  have nativeSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
    caller.checked.native.machine.heap heap before.core marked preparationPost.effects.keeps slots
  have currentSlots := SourcePruningEnumerationSharedPreparedRecursive.render_stable_slots
    heap before.core entered.core valid marked stable nativeSlots
  have markedFields (tagged : marked uv) := SourcePruningEnumerationSharedPreparedRecursive.prepared_marked_fields
    preparationFuel preparationFuel uv handle scs caller before entered decoded value heap valid marked slots stored
    decodedLookup (preparationRun 0) tagged
  by_cases empty : value = .empty
  · subst value
    let folded : Fold := .complete [.rejected preparedCaller memos.query entered] [] preparedCaller memos.query
    have finalGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
    have resources : OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv folded) := by
      refine ⟨?_, ?_⟩
      · change OutcomeResources (Typing := Typing) formulas solver caller
          (nodePlan limit own limit ceiling ceiling continuation start) (.complete [] preparedCaller memos.query)
        refine ⟨preparedCaller, inventory, memos, preparationPost, currentFits.mono finalGrowth.1, ?_, rfl, rfl, ?_⟩
        · intro key edge found
          exact finalGrowth.2 (currentKnown key edge found)
        · intro output member
          cases member
      · intro output member
        change output ∈ ([] : List (Output (bits + 2) Typing)) at member
        cases member
    refine ⟨preparationFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done .empty heap)), folded, ?_, resources⟩
    intro extra
    unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
    rw [preparationRun extra]
    cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
      simp only [terminal, Bool.false_eq_true, ↓reduceIte, frame,
        SourcePruningEnumerationSharedSelectedOpaqueDispatch.empty,
        SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, folded, preparedCaller]
  by_cases ordinary : ∃ entry rows depth free,
      value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
  · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
    subst value
    let captured := preparedCaller.checked.native.machine.heap
    obtain ⟨heights, shapes⟩ := SourcePruningEnumerationSharedEagerCapturedBounds.captured_payload_bounds
      start captured enteredPacket.context.ready.semantic.ready.semantic.1.normal.facts.linked
      (SourceCurrentConstrainedCapRequiredResources.of_checked currentFits) currentKnown
    have nodeHeight := heights (.node entry rows depth free) available
    have positive : 0 < limit := by
      change MergedOrdinaryHeight.edgesHeight rows + 1 ≤ limit at nodeHeight
      omega
    let height := limit - 1
    have heightSame : height + 1 = limit := by dsimp only [height]; omega
    have ranked : MergedOrdinaryHeight.height (.node entry rows depth free) ≤ height + 1 := by
      rw [heightSame]
      exact nodeHeight
    have computed : nodeReserved bits limit own (height + 1) ceiling ceiling continuation admitted start := by
      rw [heightSame]
      exact planned
    unfold nodeReserved at computed
    let first := fallbackPlan ceiling ceiling continuation start
    let row := fun current => tuplePlan (nodePlan limit own height) limit (ceiling + own) ceiling continuation current
    have firstGrowth := fallbackPlan_ge ceiling ceiling continuation growth start
    have firstKnown : Heap (fun guard => guard ∈ first.1) preparedCaller.checked.native.machine.heap := by
      intro key edge found
      exact firstGrowth.2 (currentKnown key edge found)
    have rowReserved : ∀ index, index < limit →
        tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
          limit (ceiling + own) ceiling continuation admitted (iterate row first index) := computed.2
    have length : (edgesOf (.node entry rows depth free)).length ≤ limit :=
      Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
    have bounded : ∀ sc ∈ scs, sc.var < entered.core.counter :=
      enteredReady.safe.1.values _ (List.mem_of_getElem? enteredStored)
    have pending := EnumerationReferences.pending_inputs entered.core enteredPacket.pending uv (some handle) scs enteredStored
    have rowFields : marked uv → ∀ edge ∈ edgesOf (.node entry rows depth free),
        SourceSynthesisHereditaryProgramFields.EdgeFields valid SourceSynthesisLabelProgramBuildRoles.literal edge := by
      intro tagged edge member
      have actualFields := (markedFields tagged).1
      cases actualFields with
      | node _ _ _ _ checked => exact checked edge (selectionMembers entry rows depth free edge member)
    obtain ⟨branchFuel, outcome, branchRun, certificate⟩ := eager_program_captured_rows_resources_with_isolated_except
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      captured limit own height limit valid marked inventory preparedCaller memos metadata entered first ceiling ceiling scs uv handle
      enteredPacket enteredReady enteredStored enteredIncoming (currentFits.mono firstGrowth.1) firstKnown
      (SourceEqualityRequiredCache.pure_keeps captured enteredPacket.context.ready.semantic.ready)
      currentMass bucketBound entry rows depth free available closed ranked bounded pending currentSlots
      (edgesOf (.node entry rows depth free)) length (selectionMembers entry rows depth free) rowFields shapes
      selectionMembers selectionLength rowReserved
    have originalOutputs :
        ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted (finish uv outcome),
          programOutputRolesWithIsolatedExcept valid marked caller before uv output := by
      intro output member
      obtain ⟨roles, markers⟩ := certificate.2 output member
      refine ⟨roles, ?_⟩
      intro held heldHandle heldValue different isolated decoded boundary
      have enteredIsolated := isolated.through_renderStable stable
      have enteredLookup := SourcePruningEnumerationNodes.lookupNode_keeps
        caller.checked.native.machine.heap heap preparationPost.effects.keeps heldHandle heldValue decoded
      exact markers held heldHandle heldValue different enteredIsolated enteredLookup boundary
    have certificate : OutcomeResourcesWithOutputs
        (programOutputRolesWithIsolatedExcept valid marked caller before uv)
        formulas solver preparedCaller (iterate row first limit) (finish uv outcome) :=
      ⟨certificate.1, originalOutputs⟩
    have finalSame : eagerFinal (recursiveDepth + 1) seed ceiling = iterate row first limit := by
      change nodePlan limit own limit ceiling ceiling continuation start = _
      calc
        nodePlan limit own limit ceiling ceiling continuation start =
            nodePlan limit own (height + 1) ceiling ceiling continuation start :=
          congrArg (fun h => nodePlan limit own h ceiling ceiling continuation start) heightSame.symm
        _ = iterate row first limit := by
          unfold nodePlan
          rfl
    have resources : OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) := by
      rw [finalSame]
      exact resources_outputs_post preparationPost certificate
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done (.node entry rows depth free) heap)),
      outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have atBranch := branchRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at atBranch
    unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
    rw [atPreparation]
    simp only [nonterminal, Bool.false_eq_true, ↓reduceIte]
    rw [frame, atBranch]
  · have dispatch : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false := by
      cases value with
      | node entry rows depth free =>
          cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
          | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
          | true => rfl
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ => rfl
    have unmarked : ¬marked uv := by
      intro tagged
      have currentFields := markedFields tagged
      have fields := currentFields.1
      cases fields with
      | empty => exact empty rfl
      | node entry rows depth free _checked =>
          exact ordinary ⟨entry, rows, depth, free, rfl,
            eager_program_annotation_nonterminal scs currentFields.2.2⟩
    obtain ⟨branchFuel, receipt, outcome, rawRun, receiptRun, certificate⟩ := eager_program_opaque_resources_with_isolated_except
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      inventory preparedCaller memos metadata entered start ceiling ceiling uv handle scs value enteredPacket enteredReady
      enteredStored enteredIncoming available closed dispatch currentFits currentKnown currentMass bucketBound
      selectionMembers selectionLength (nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned)
      valid marked currentSlots unmarked
    have originalOutputs :
        ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted (finish uv outcome),
          programOutputRolesWithIsolatedExcept valid marked caller before uv output := by
      intro output member
      obtain ⟨roles, markers⟩ := certificate.2 output member
      refine ⟨roles, ?_⟩
      intro held heldHandle heldValue different isolated decoded boundary
      have enteredIsolated := isolated.through_renderStable stable
      have enteredLookup := SourcePruningEnumerationNodes.lookupNode_keeps
        caller.checked.native.machine.heap heap preparationPost.effects.keeps heldHandle heldValue decoded
      exact markers held heldHandle heldValue different enteredIsolated enteredLookup boundary
    have certificate : OutcomeResourcesWithOutputs
        (programOutputRolesWithIsolatedExcept valid marked caller before uv)
        formulas solver preparedCaller (fallbackPlan ceiling ceiling continuation start) (finish uv outcome) :=
      ⟨certificate.1, originalOutputs⟩
    have enlarged := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
    have resources : OutcomeResourcesWithOutputs (programOutputRolesWithIsolatedExcept valid marked caller before uv) formulas solver caller
        (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) :=
      resources_outputs_post preparationPost (resources_outputs_mono enlarged.1 enlarged.2 certificate)
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)), outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have rawAt := rawRun (preparationFuel + extra)
    have continued := receiptRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at rawAt continued
    have composed : SourcePruningEnumerationSharedReceiptContinuation.run
        (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query) = outcome := by
      rw [rawAt]
      exact continued
    have actual : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) edgesOf)
        (hook (preparationFuel + branchFuel + extra)) checkEmpty
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) uv edgesOf caller before memos.query =
      (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)),
        some (SourcePruningEnumerationSharedReceiptContinuation.run
          (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
          (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query))) := by
      unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      rw [atPreparation]
      cases value with
      | node entry rows depth free =>
          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, here⟩).elim
            | true => rfl
          simp only [terminal, ↓reduceIte, frame, preparedCaller]
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
            simp only [here, Bool.false_eq_true, ↓reduceIte, frame, preparedCaller]
    rw [composed] at actual
    exact actual
end ActualProgramPreparedResources

section ActualProgramEagerExpansion
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationSelectedStep (runPrefix)
open SourcePruningEnumerationSharedRecursive (checkpoint_resources CurrentPrefixFacts)
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound

private theorem eager_program_expansion_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome := by
  have beforeReady := (SourcePruningEnumerationRestart.selected stop order metadata caller before uv
    packet.valid packet.safe chosen).1
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  have firstReserved := nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned
  have finalGrowth := eagerFinal_ge (recursiveDepth + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
  have stageGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
  obtain ⟨currentFuel, phases⟩ := checkpoint_resources holeKey keyMatches admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  obtain ⟨legacyFuel, legacyComplete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet
  let prefixFuel := currentFuel + legacyFuel
  have shift (extra : Nat) : currentFuel + (legacyFuel + extra) = prefixFuel + extra := by
    dsimp only [prefixFuel]
    omega
  have legacy (extra : Nat) : SourcePruningEnumerationSelectedStep.PrefixValid
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + extra) uv caller before memos
      (runPrefix holeKey keyMatches admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query) := by
    have prefixReceipt := legacyComplete (currentFuel + extra) uv chosen
    have common : legacyFuel + (currentFuel + extra) = prefixFuel + extra := by
      dsimp only [prefixFuel]
      omega
    simpa only [common] using prefixReceipt
  rcases phases with ⟨checked, originalPhase⟩ | ⟨checked, heap, originalPhase⟩ |
    ⟨checked, phaseValue, heap, after, _nonempty, originalPhase⟩
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have prefixReceipt := legacy 0
    rw [(phase 0).1] at prefixReceipt
    have checkedSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
        SourceSynthesisLabelProgramBuildRoles.literal caller.checked.native.machine.heap checked.core marked :=
      SourcePruningEnumerationSharedPreparedRecursive.observed_prefix_slots
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (prefixFuel + 0) uv caller memos before packet beforeReady valid marked slots
        _ prefixReceipt (phase 0).1
    have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet _ prefixReceipt (phase 0).1
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
    · have certificate : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked)
          formulas solver caller seed (.complete [] caller memos.query) := by
        constructor
        · refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim
        · intro output member
          cases member
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_,
        resources_outputs_mono finalGrowth.1 finalGrowth.2 certificate⟩
      intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, observed]
    · let parkedSeed := advance start (ceiling + 1)
      let parkedMass := ceiling + ceiling
      have headGrowth : Le start.2 parkedSeed.2 ∧ start.1 ⊆ parkedSeed.1 :=
        ⟨SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge start (ceiling + 1),
          SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge start (ceiling + 1)⟩
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : mass checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound firstReserved.2 valid marked checkedSlots
      have included := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
      have callbackResources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
          (fallbackPlan ceiling ceiling continuation start) outcome := resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, resources_outputs_mono included.1 included.2 callbackResources⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, observed]
      dsimp only
      rw [framed]
      exact actual
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
    have certificate : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked)
        formulas solver caller start (.complete [] reached memos.query) := by
      constructor
      · refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
          current.2.2, rfl, query.symm, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      · intro output member
        cases member
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, (phase extra).1]
    · exact resources_outputs_mono stageGrowth.1 stageGrowth.2 certificate
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨_action, prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      CurrentPrefixFacts.right_packet current.1
    have prefixReceipt := legacy 0
    rw [prefixAt] at prefixReceipt
    have afterSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
        SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap after.core marked :=
      SourcePruningEnumerationSharedPreparedRecursive.observed_prefix_slots
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (prefixFuel + 0) uv caller memos before packet beforeReady valid marked slots
        _ prefixReceipt prefixAt
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ prefixReceipt
    obtain ⟨handle, scs, _value, _oldMemos, _oldPost, _oldQuery, _oldPacket, ready, stored,
      _decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      _oldFits, _oldKnown⟩ := admission
    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
        reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : mass after.core ≤ ceiling := Nat.le_trans
      (SourcePruningEnumerationPrefixMass.retained_le holeKey keyMatches admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ prefixReceipt prefixAt)
      initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    obtain ⟨scanFuel, _observation, result, scanRun, certificate⟩ := eager_program_prepared_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      inventory reached middleMemos metadata after seed ceiling uv handle scs middlePacket ready stored incoming
      middleFits middleKnown currentMass inheritedLength selectionMembers selectionLength reserved valid marked afterSlots
    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, resources_outputs_post middlePost certificate⟩
    intro extra
    obtain ⟨currentAction, currentPrefix, _current⟩ := phase (scanFuel + extra)
    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [common] at currentPrefix
    have actual := scanRun (prefixFuel + extra)
    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [scanCommon, middleQuery] at actual
    rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
      ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, currentPrefix]
    dsimp only
    dsimp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] at actual
    rw [actual]


-- The actual expansion retains every original isolated marker.
private theorem eager_program_expansion_resources_with_isolated
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeWithIsolatedComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRolesWithIsolated valid marked caller before) formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome := by
  have beforeReady := (SourcePruningEnumerationRestart.selected stop order metadata caller before uv
    packet.valid packet.safe chosen).1
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  have firstReserved := nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned
  have finalGrowth := eagerFinal_ge (recursiveDepth + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
  have stageGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
  obtain ⟨currentFuel, phases⟩ := checkpoint_resources holeKey keyMatches admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  obtain ⟨legacyFuel, legacyComplete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet
  let prefixFuel := currentFuel + legacyFuel
  have shift (extra : Nat) : currentFuel + (legacyFuel + extra) = prefixFuel + extra := by
    dsimp only [prefixFuel]
    omega
  have legacy (extra : Nat) : SourcePruningEnumerationSelectedStep.PrefixValid
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + extra) uv caller before memos
      (runPrefix holeKey keyMatches admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query) := by
    have prefixReceipt := legacyComplete (currentFuel + extra) uv chosen
    have common : legacyFuel + (currentFuel + extra) = prefixFuel + extra := by
      dsimp only [prefixFuel]
      omega
    simpa only [common] using prefixReceipt
  rcases phases with ⟨checked, originalPhase⟩ | ⟨checked, heap, originalPhase⟩ |
    ⟨checked, phaseValue, heap, after, _nonempty, originalPhase⟩
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have prefixReceipt := legacy 0
    rw [(phase 0).1] at prefixReceipt
    have checkedSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
        SourceSynthesisLabelProgramBuildRoles.literal caller.checked.native.machine.heap checked.core marked :=
      SourcePruningEnumerationSharedPreparedRecursive.observed_prefix_slots
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (prefixFuel + 0) uv caller memos before packet beforeReady valid marked slots
        _ prefixReceipt (phase 0).1
    have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet _ prefixReceipt (phase 0).1
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
    · have certificate : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRolesWithIsolated valid marked caller before)
          formulas solver caller seed (.complete [] caller memos.query) := by
        constructor
        · refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim
        · intro output member
          cases member
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_,
        resources_outputs_mono finalGrowth.1 finalGrowth.2 certificate⟩
      intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, observed]
    · let parkedSeed := advance start (ceiling + 1)
      let parkedMass := ceiling + ceiling
      have headGrowth : Le start.2 parkedSeed.2 ∧ start.1 ⊆ parkedSeed.1 :=
        ⟨SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge start (ceiling + 1),
          SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge start (ceiling + 1)⟩
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : mass checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound firstReserved.2 valid marked checkedSlots
      have included := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
      have originalOutputs :
          ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted outcome,
            programOutputRolesWithIsolated valid marked caller before output := by
        intro output member
        obtain ⟨roles, markers⟩ := resources.2 output member
        refine ⟨roles, ?_⟩
        intro held heldHandle heldValue isolated decoded boundary
        have retained := SourcePruningEnumerationSelectedStep.prefix_isolated
          holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata
          formulas solver inventory (prefixFuel + 0) uv caller before memos held heldHandle heldValue
          packet isolated decoded boundary chosen (legacy 0)
        rw [(phase 0).1] at retained
        exact markers held heldHandle heldValue retained decoded boundary
      have resources : OutcomeResourcesWithOutputs
          (programOutputRolesWithIsolated valid marked caller before)
          formulas solver caller (eagerFinal recursiveDepth parkedSeed parkedMass) outcome :=
        ⟨resources.1, originalOutputs⟩
      have callbackResources : OutcomeResourcesWithOutputs (programOutputRolesWithIsolated valid marked caller before) formulas solver caller
          (fallbackPlan ceiling ceiling continuation start) outcome := resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, resources_outputs_mono included.1 included.2 callbackResources⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, observed]
      dsimp only
      rw [framed]
      exact actual
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
    have certificate : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRolesWithIsolated valid marked caller before)
        formulas solver caller start (.complete [] reached memos.query) := by
      constructor
      · refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
          current.2.2, rfl, query.symm, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      · intro output member
        cases member
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
        SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, (phase extra).1]
    · exact resources_outputs_mono stageGrowth.1 stageGrowth.2 certificate
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨_action, prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      CurrentPrefixFacts.right_packet current.1
    have prefixReceipt := legacy 0
    rw [prefixAt] at prefixReceipt
    have afterSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
        SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap after.core marked :=
      SourcePruningEnumerationSharedPreparedRecursive.observed_prefix_slots
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (prefixFuel + 0) uv caller memos before packet beforeReady valid marked slots
        _ prefixReceipt prefixAt
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ prefixReceipt
    obtain ⟨handle, scs, _value, _oldMemos, _oldPost, _oldQuery, _oldPacket, ready, stored,
      _decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      _oldFits, _oldKnown⟩ := admission
    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
        reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : mass after.core ≤ ceiling := Nat.le_trans
      (SourcePruningEnumerationPrefixMass.retained_le holeKey keyMatches admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ prefixReceipt prefixAt)
      initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    obtain ⟨scanFuel, _observation, result, scanRun, certificate⟩ := eager_program_prepared_resources_with_isolated_except
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      inventory reached middleMemos metadata after seed ceiling uv handle scs middlePacket ready stored incoming
      middleFits middleKnown currentMass inheritedLength selectionMembers selectionLength reserved valid marked afterSlots
    have originalOutputs :
        ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted (finish uv result),
          programOutputRolesWithIsolated valid marked caller before output := by
      intro output member
      obtain ⟨roles, markers⟩ := certificate.2 output member
      refine ⟨roles, ?_⟩
      intro held heldHandle heldValue isolated decoded boundary
      have different := EnumerationDischargeHistory.packet_restart_ne
        formulas solver inventory caller memos metadata before held heldHandle uv heldValue
        stop order packet isolated decoded boundary chosen
      have retained := SourcePruningEnumerationSelectedStep.prefix_isolated
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (prefixFuel + 0) uv caller before memos held heldHandle heldValue
        packet isolated decoded boundary chosen (legacy 0)
      rw [prefixAt] at retained
      have reachedLookup := SourcePruningEnumerationNodes.lookupNode_keeps
        caller.checked.native.machine.heap reached.checked.native.machine.heap
        middlePost.effects.keeps heldHandle heldValue decoded
      exact markers held heldHandle heldValue (Ne.symm different) retained reachedLookup boundary
    have certificate : OutcomeResourcesWithOutputs
        (programOutputRolesWithIsolated valid marked caller before)
        formulas solver reached (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv result) :=
      ⟨certificate.1, originalOutputs⟩
    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, resources_outputs_post middlePost certificate⟩
    intro extra
    obtain ⟨currentAction, currentPrefix, _current⟩ := phase (scanFuel + extra)
    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [common] at currentPrefix
    have actual := scanRun (prefixFuel + extra)
    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [scanCommon, middleQuery] at actual
    rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
      ← SourcePruningEnumerationSelectedStep.runPrefix_configured_eq, currentPrefix]
    dsimp only
    dsimp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] at actual
    rw [actual]

end ActualProgramEagerExpansion

section ActualEagerProgramDepthClosure
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_resume_complete
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) :
    EagerProgramResumeComplete (Typing := Typing) (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth := by
  induction recursiveDepth with
  | zero =>
      exact eager_program_resume_zero_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver
  | succ depth ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved valid marked slots
      have growth := eagerFinal_ge (depth + 1) seed ceiling
      cases decision : SourcePruningEnumerationRestart.decision stop order metadata before with
      | none =>
          obtain ⟨fuel, outcome, running, resources⟩ :=
            (eager_program_resume_zero_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver)
              inventory caller memos before metadata seed ceiling packet bounded known
              selectionMembers selectionLength initialMass (by trivial) valid marked slots
          refine ⟨fuel, outcome, ?_, resources_outputs_mono growth.1 growth.2 resources⟩
          intro extra
          simpa only [decision, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
            SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
      | some selected =>
          cases selected with
          | done =>
              obtain ⟨fuel, outcome, running, resources⟩ :=
                (eager_program_resume_zero_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver)
                  inventory caller memos before metadata seed ceiling packet bounded known
                  selectionMembers selectionLength initialMass (by trivial) valid marked slots
              refine ⟨fuel, outcome, ?_, resources_outputs_mono growth.1 growth.2 resources⟩
              intro extra
              simpa only [decision, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | stuck =>
              obtain ⟨fuel, outcome, running, resources⟩ :=
                (eager_program_resume_zero_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver)
                  inventory caller memos before metadata seed ceiling packet bounded known
                  selectionMembers selectionLength initialMass (by trivial) valid marked slots
              refine ⟨fuel, outcome, ?_, resources_outputs_mono growth.1 growth.2 resources⟩
              intro extra
              simpa only [decision, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | expand uv =>
              exact eager_program_expansion_resources holeKey keyMatches admits graph templates checkEmpty edgesOf stop order
                formulas solver depth ih inventory caller memos before metadata uv seed ceiling packet bounded known
                selectionMembers selectionLength initialMass reserved decision valid marked slots


-- Every depth retains Program roles and all original isolated markers.
private theorem eager_program_resume_with_isolated_complete
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) :
    EagerProgramResumeWithIsolatedComplete (Typing := Typing) (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth := by
  induction recursiveDepth with
  | zero =>
      exact eager_program_resume_zero_with_isolated_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver
  | succ depth ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved valid marked slots
      have growth := eagerFinal_ge (depth + 1) seed ceiling
      cases decision : SourcePruningEnumerationRestart.decision stop order metadata before with
      | none =>
          obtain ⟨fuel, outcome, running, resources⟩ :=
            (eager_program_resume_zero_with_isolated_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver)
              inventory caller memos before metadata seed ceiling packet bounded known
              selectionMembers selectionLength initialMass (by trivial) valid marked slots
          refine ⟨fuel, outcome, ?_, resources_outputs_mono growth.1 growth.2 resources⟩
          intro extra
          simpa only [decision, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
            SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
      | some selected =>
          cases selected with
          | done =>
              obtain ⟨fuel, outcome, running, resources⟩ :=
                (eager_program_resume_zero_with_isolated_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver)
                  inventory caller memos before metadata seed ceiling packet bounded known
                  selectionMembers selectionLength initialMass (by trivial) valid marked slots
              refine ⟨fuel, outcome, ?_, resources_outputs_mono growth.1 growth.2 resources⟩
              intro extra
              simpa only [decision, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | stuck =>
              obtain ⟨fuel, outcome, running, resources⟩ :=
                (eager_program_resume_zero_with_isolated_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver)
                  inventory caller memos before metadata seed ceiling packet bounded known
                  selectionMembers selectionLength initialMass (by trivial) valid marked slots
              refine ⟨fuel, outcome, ?_, resources_outputs_mono growth.1 growth.2 resources⟩
              intro extra
              simpa only [decision, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow] using running extra
          | expand uv =>
              exact eager_program_expansion_resources_with_isolated holeKey keyMatches admits graph templates checkEmpty edgesOf stop order
                formulas solver depth ih inventory caller memos before metadata uv seed ceiling packet bounded known
                selectionMembers selectionLength initialMass reserved decision valid marked slots

/-- Current slots give one stable eager result and slots for each emitted output. -/
theorem runEager_finite_complete_resources_program_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ bound outcome,
      ((∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome) ∧
      ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted outcome,
        ∃ finalMarked : Nat → Prop,
          (∀ uv, marked uv → finalMarked uv) ∧
          SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
            output.caller.checked.native.machine.heap output.cache.core finalMarked := by
  have complete := eager_program_resume_complete (Typing := Typing) (bits := bits) holeKey fits admits graph templates
    checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨fuel, outcome, running, resources⟩ := complete inventory caller memos before metadata seed ceiling
    packet bounded known selectionMembers selectionLength initialMass reserved valid marked slots
  exact ⟨fuel, outcome, ⟨fun extra => running extra, resources.1⟩, resources.2⟩

/-- Each output retains Program slots and each original isolated boundary. -/
theorem runEager_finite_complete_resources_program_slots_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ bound outcome,
      ((∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome) ∧
      ∀ output ∈ SourcePruningEnumerationSharedPreparedRecursive.emitted outcome,
        (∃ finalMarked : Nat → Prop,
          (∀ uv, marked uv → finalMarked uv) ∧
          SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
            output.caller.checked.native.machine.heap output.cache.core finalMarked) ∧
        ∀ held handle (value : Node),
          EnumerationDischargeHistory.IsolatedPending held handle before.core →
          SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some value →
          MergedOrdinaryHeight.recursiveBoundary value = true →
          EnumerationDischargeHistory.IsolatedPending held handle output.cache.core ∧
            SourcePruningEnumerationNodes.lookupNode output.caller.checked.native.machine.heap handle = some value := by
  have complete := eager_program_resume_with_isolated_complete (Typing := Typing) (bits := bits) holeKey fits admits graph templates
    checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨fuel, outcome, running, resources⟩ := complete inventory caller memos before metadata seed ceiling
    packet bounded known selectionMembers selectionLength initialMass reserved valid marked slots
  exact ⟨fuel, outcome, ⟨fun extra => running extra, resources.1⟩, resources.2⟩

end ActualEagerProgramDepthClosure

end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualIdentityEmittedPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure OutputResources OutcomeResources emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (runEagerWithNarrow runWithNarrow resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "IdentityOutcome" =>
  SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
    (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile

/-- Outputs retain resources. Only a complete outcome must certify its final endpoint. -/
private def IdentityEmittedCompleteResources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (seed : Seed) (outcome : IdentityOutcome) : Prop :=
  (∀ output ∈ emitted outcome, OutputResources formulas solver original seed output) ∧
    match outcome with
    | .complete _ _ _ => OutcomeResources formulas solver original seed outcome
    | .stopped _ _ _ => True

/-- The internal induction target uses the actual worker at each supplied work bound. -/
private def IdentityEagerEmittedCompleteAtDepth
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveDepth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Unit) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    eagerReserved bits recursiveDepth seed ceiling →
    ∀ workFuel, IdentityEmittedCompleteResources formulas solver caller
      (eagerFinal recursiveDepth seed ceiling)
      (runEagerWithNarrow (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) workFuel recursiveDepth metadata caller memos.query before)

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- Whole outcome resources supply outputs and complete endpoints. -/
private theorem identity_emitted_complete_of_outcome
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {original : Caller (bits + 2)} {seed : Seed} {outcome : IdentityOutcome}
    (resources : OutcomeResources formulas solver original seed outcome) :
    IdentityEmittedCompleteResources formulas solver original seed outcome := by
  constructor
  · obtain ⟨_reached, _next, _final, _post, _bounded, _known, shape⟩ := resources
    cases outcome with
    | complete outputs caller queries => exact shape.2.2
    | stopped outputs reason endpoint => exact shape.2
  · cases outcome with
    | complete outputs caller queries => exact resources
    | stopped outputs reason endpoint => trivial

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- Forecast growth retains outputs and an actual complete endpoint. -/
private theorem identity_emitted_complete_mono
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {original : Caller (bits + 2)} {seed larger : Seed} {outcome : IdentityOutcome}
    (numeric : Le seed.2 larger.2) (alphabet : seed.1 ⊆ larger.1)
    (resources : IdentityEmittedCompleteResources formulas solver original seed outcome) :
    IdentityEmittedCompleteResources formulas solver original larger outcome := by
  obtain ⟨outputsValid, completed⟩ := resources
  constructor
  · intro output member
    exact (outputsValid output member).mono numeric alphabet
  · cases outcome with
    | complete outputs caller queries => exact completed.mono numeric alphabet
    | stopped outputs reason endpoint => trivial

/-- Zero recursive depth certifies each actual work bound. -/
private theorem identity_emitted_resources_zero
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    IdentityEagerEmittedCompleteAtDepth (bits := bits) graph checkEmpty edgesOf formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength _initialMass _reserved workFuel
  obtain ⟨outcome, running, resources⟩ := identity_resume_eager_zero_resources
    graph checkEmpty edgesOf formulas solver inventory caller memos before metadata
    (SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before)
    seed packet bounded known
  have actual : runEagerWithNarrow (fun _ _ _ node state => .done node state)
      graph [] checkEmpty edgesOf none (fun _ _ => none) workFuel 0
      metadata caller memos.query before = outcome := running workFuel
  simpa only [eagerFinal, actual] using identity_emitted_complete_of_outcome resources

set_option maxHeartbeats 2000000 in
/-- An actual parked prefix uses the resource induction at a smaller recursive depth. -/
private theorem identity_parked_prefix_emitted_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveDepth : Nat)
    (recursive : IdentityEagerEmittedCompleteAtDepth (bits := bits)
      graph checkEmpty edgesOf formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Unit) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (workFuel uv : Nat)
    (chosen : SourcePruningEnumerationRestart.decision none (fun _ _ => none)
      metadata before = some (.expand uv))
    (parked : ∃ checked candidate raw,
      SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .parked checked candidate raw) :
    IdentityEmittedCompleteResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling)
      (runEagerWithNarrow (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) workFuel (recursiveDepth + 1) metadata caller memos.query before) := by
  obtain ⟨checked, candidate, raw, observedPrefix⟩ := parked
  have phases := SourcePruningEnumerationSharedRecursive.prefix_identity_phase_resources_at_any_budget
    graph metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known workFuel uv chosen
  dsimp only at phases
  rw [observedPrefix] at phases
  cases candidate with
  | none =>
      unfold runEagerWithNarrow runWithNarrow
      rw [chosen, resumeWithNarrow, observedPrefix]
      constructor
      · intro output member
        cases member
      · trivial
  | some parkedCache =>
      dsimp only at phases
      rcases phases with ⟨after, _ready, _incoming, checkedMass, phase, current⟩ |
        emptyPhase | nonemptyPhase
      · have facts := current.1
        rw [phase] at facts
        obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
        have same : after = cached := Option.some.inj sameCache
        subst cached
        have framed : EnumerationExpandableIndex.frame after.core after = after := by
          cases after
          rfl
        have actualPrefix := observedPrefix.trans phase
        by_cases blocked : SourcePruningEnumerationRestart.decision none (fun _ _ => none)
            metadata after = some .stuck
        · have certificate : OutcomeResources (Typing := Unit) formulas solver caller seed
              (.complete [] caller memos.query) := by
            refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
            intro output member
            cases member
          have finalGrowth := eagerFinal_ge (recursiveDepth + 1) seed ceiling
          rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at actualPrefix
          unfold runEagerWithNarrow runWithNarrow
          rw [chosen, resumeWithNarrow, actualPrefix]
          exact identity_emitted_complete_of_outcome (certificate.mono finalGrowth.1 finalGrowth.2)
        · let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
          let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
          let own := SourcePruningEnumerationGuardWidth.width start.1
          let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
          let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
          have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
              current.1 ⊆ (continuation retained current).1 :=
            fun retained current => eagerFinal_ge recursiveDepth current retained
          have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
            exact reserved
          have firstReserved := nodeReserved_fallback bits limit own limit ceiling ceiling
            continuation admitted start planned
          let parkedSeed := advance start (ceiling + 1)
          let parkedMass := ceiling + ceiling
          have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
          have headGrowth : Le start.2 parkedSeed.2 ∧ start.1 ⊆ parkedSeed.1 :=
            ⟨SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge start (ceiling + 1),
              SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge start (ceiling + 1)⟩
          have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
          have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
            fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
          have massBound : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ parkedMass :=
            Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
          have inherited := recursive inventory caller memos after metadata parkedSeed parkedMass
            checkedPacket parkedFits parkedKnown selectionMembers selectionLength massBound firstReserved.2 workFuel
          have included := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
          have lifted : IdentityEmittedCompleteResources formulas solver caller
              (eagerFinal (recursiveDepth + 1) seed ceiling)
              (runEagerWithNarrow (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
                none (fun _ _ => none) workFuel recursiveDepth metadata caller memos.query after) :=
            identity_emitted_complete_mono included.1 included.2 inherited
          have sameRun :
              runEagerWithNarrow (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
                  none (fun _ _ => none) workFuel (recursiveDepth + 1) metadata caller memos.query before =
                runEagerWithNarrow (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
                  none (fun _ _ => none) workFuel recursiveDepth metadata caller memos.query after := by
            rw [SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at actualPrefix
            unfold runEagerWithNarrow runWithNarrow
            rw [chosen, resumeWithNarrow, actualPrefix]
            dsimp only
            rw [framed]
          rw [sameRun]
          exact lifted
      · obtain ⟨_emptyCore, _emptyReady, _emptyIncoming, _emptyMass, impossible, _emptyResources⟩ := emptyPhase
        cases impossible
      · obtain ⟨_handle, _scs, _value, _after, _nonempty, _encoded, _afterReady, _stored,
          _afterIncoming, _lengths, _sameMass, impossible, _nonemptyResources⟩ := nonemptyPhase
        cases impossible

end ActualIdentityEmittedPrefix
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualIdentityCallbackPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output OutputResources OutcomeResources emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (runEagerWithNarrow runWithNarrow resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- An earlier native Post retains the same actual outputs and complete endpoint. -/
private theorem identity_emitted_complete_post
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {original middle : Caller (bits + 2)} {next : Inventory} {final : Memos}
    {seed : Seed}
    {outcome : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
      (Output (bits + 2) Unit) (SourcePruningEnumerationSharedPreparedRecursive.Failure (bits + 2) Unit) (bits + 2)}
    (post : Post formulas solver next original middle final)
    (resources : IdentityEmittedCompleteResources formulas solver middle seed outcome) :
    IdentityEmittedCompleteResources formulas solver original seed outcome := by
  obtain ⟨outputsValid, completed⟩ := resources
  constructor
  · intro output member
    exact (outputsValid output member).post post
  · cases outcome with
    | complete outputs caller queries => exact completed.post post
    | stopped outputs reason endpoint => trivial

/-- The actual empty-catalog callback uses the same work bound at smaller recursive depth. -/
private theorem identity_callback_emitted_complete_at_any_budget
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveDepth : Nat)
    (recursive : IdentityEagerEmittedCompleteAtDepth (bits := bits)
      graph checkEmpty edgesOf formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (before : Cached) (metadata : Metadata Unit) (uv : Nat) (fragment : Fragment)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling) (workFuel : Nat) :
    IdentityEmittedCompleteResources formulas solver caller (eagerFinal recursiveDepth seed ceiling)
      (SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (resumeWithNarrow (Typing := Unit) (width := bits + 2)
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
          none (fun _ _ => none) workFuel recursiveDepth)
        graph [] none (fun _ _ => none) workFuel metadata uv fragment caller memos.query before) := by
  let updated : Metadata Unit :=
    {metadata with types := SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment)}
  have updatedPacket : Packet formulas solver inventory caller memos updated before :=
    ⟨packet.context, packet.safe, packet.pending, packet.valid, packet.ordered, packet.bounded⟩
  have inherited := recursive inventory caller memos before updated seed ceiling
    updatedPacket bounded known selectionMembers selectionLength mass reserved workFuel
  let recur := resumeWithNarrow (Typing := Unit) (width := bits + 2)
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
      workFuel workFuel workFuel workFuel workFuel edgesOf)
    (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
    none (fun _ _ => none) workFuel recursiveDepth
  have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph [] workFuel
      metadata uv (.inl fragment) before.core) = [.ok ((false, updated), before.core)] := by
    rw [SourcePruningRecordTypes.recordTypes_empty]
    rfl
  have actual := SourcePruningEnumerationSharedPreparedRecursive.continue_recorded
    recur graph [] none (fun _ _ => none) workFuel metadata updated uv fragment caller
    memos.query before before.core recorded
  have framed : EnumerationExpandableIndex.frame before.core before = before := by
    cases before
    rfl
  change IdentityEmittedCompleteResources formulas solver caller (eagerFinal recursiveDepth seed ceiling)
    (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph [] none (fun _ _ => none)
      workFuel metadata uv fragment caller memos.query before)
  rw [actual]
  simpa only [framed, runEagerWithNarrow, runWithNarrow, recur] using inherited

/-- An actual completed callback supplies the next captured sibling packet and native resources. -/
private theorem identity_completed_callback_captured_resources_at_any_budget
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveDepth : Nat)
    (recursive : IdentityEagerEmittedCompleteAtDepth (bits := bits)
      graph checkEmpty edgesOf formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (before : Cached) (metadata : Metadata Unit) (uv : Nat) (fragment : Fragment)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling) (workFuel : Nat)
    (outputs : List (Output (bits + 2) Unit)) (reached : Caller (bits + 2)) (saved : SourceEndpointMemo.Memos)
    (observed : SourcePruningEnumerationSharedPreparedRecursive.continueWith
      (resumeWithNarrow (Typing := Unit) (width := bits + 2)
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          workFuel workFuel workFuel workFuel workFuel edgesOf)
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) workFuel recursiveDepth)
      graph [] none (fun _ _ => none) workFuel metadata uv fragment caller memos.query before =
        .complete outputs reached saved) :
    ∃ (next : Inventory) (final : Memos),
      Post formulas solver next caller reached final ∧ final.query = saved ∧
      Packet formulas solver next reached final metadata before ∧
      Fits (eagerFinal recursiveDepth seed ceiling).2 reached.checked ∧
      Heap (fun guard => guard ∈ (eagerFinal recursiveDepth seed ceiling).1) reached.checked.native.machine.heap ∧
      ∀ output ∈ outputs,
        OutputResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) output := by
  have resources := identity_callback_emitted_complete_at_any_budget graph checkEmpty edgesOf
    formulas solver recursiveDepth recursive inventory caller memos before metadata uv fragment seed ceiling
    packet bounded known selectionMembers selectionLength mass reserved workFuel
  rw [observed] at resources
  exact SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet
    formulas solver inventory caller memos metadata before (eagerFinal recursiveDepth seed ceiling)
    outputs reached saved packet resources.2

end ActualIdentityCallbackPrefix
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualIdentityEmptyPreparedTuple
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure OutputResources OutcomeResources emitted finish)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile

/-- An empty actual child tuple derives its finalizer packet and same-budget recursive callback. -/
private theorem identity_empty_eager_captured_prefix_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : IdentityEagerEmittedCompleteAtDepth (bits := bits)
      graph checkEmpty edgesOf formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Unit)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (_bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (_ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (_shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (empty : edge.children = []) (workFuel : Nat) :
    IdentityEmittedCompleteResources formulas solver caller
      (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
        (fun retained current => eagerFinal recursiveDepth current retained) seed)
      (finish uv (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (resumeWithNarrow (Typing := Unit) (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              workFuel workFuel workFuel workFuel workFuel edgesOf)
            (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
            none (fun _ _ => none) workFuel recursiveDepth)
          graph [] none (fun _ _ => none) workFuel metadata uv)
        workFuel uv scs edge caller memos.query before)) := by
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let plan := tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed
  let visit := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (resumeWithNarrow (Typing := Unit) (width := bits + 2) visit
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveDepth)
    graph [] none (fun _ _ => none) workFuel metadata uv
  change IdentityEmittedCompleteResources formulas solver caller plan
    (finish uv (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
      visit hook workFuel uv scs edge caller memos.query before))
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 :=
    fun retained current => eagerFinal_ge recursiveDepth current retained
  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
    limit (bound + own) ceiling continuation growth seed
  have planFits : Fits plan.2 caller.checked := fits.mono planGrowth.1
  have planKnown : Heap (fun guard => guard ∈ plan.1) caller.checked.native.machine.heap :=
    fun key edge found => planGrowth.2 (known key edge found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
        simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
          SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
        constructor
        · intro output member
          cases member
        · trivial
    | some fields =>
        rcases fields with ⟨tries, residual⟩
        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, _lower, reducing⟩ :=
          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
        obtain ⟨_prepared, _middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, _genuine, middleProtects⟩ := ownReceipt
        have nilInputs : SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries = [] := by
          simp [SourcePruningEnumerationEdgeInputs.children, empty]
        have history : TupleInputs formulas solver caller metadata middle
            (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries)
            [] caller memos.query middle := by
          rw [nilInputs]
          exact tuple_inputs_nil formulas solver inventory caller memos metadata middle middlePacket
        have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
          middleCore middleCounter middleProtects [] caller memos.query middle history
        let fragment : Fragment := .node edge.entry.key.symbol []
        let childAfter := SelectedEdge.finish residual fragment middle
        have childMass : SourcePruningEnumerationPrefixAdmission.suspendedBound childAfter.core ≤ ceiling := by
          change SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling
          rw [middleMass]
          exact mass
        rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts, reducing, nilInputs]
        simp only [SourcePruningEnumerationSharedChildVisitors.visitChildren]
        change IdentityEmittedCompleteResources formulas solver caller plan
          (finish uv (match SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
            workFuel uv fragment childAfter with
            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook caller memos.query
                (some (.complete fragment caller memos.query finished))
            | none => SourcePruningEnumerationSharedReceiptContinuation.run hook caller memos.query
                (some (.finalizeStopped fragment caller memos.query childAfter))))
        cases observedFinish : SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
            workFuel uv fragment childAfter with
        | none =>
            constructor
            · intro output member
              cases member
            · trivial
        | some finished =>
            obtain ⟨next, final, finalFuel, canonicalAfter, _post, querySame, finalAt,
                finishedPacket, _fragmentBound, _core, finalMass, _stored, _root⟩ :=
              finalize_child_inputs_packet formulas solver caller caller metadata before childAfter uv handle scs
                fragment memos.query ready stored incoming data
            have observedLater := SourcePruningEnumerationFinalize.run_some_moreFuel
              caller.checked.native.machine.heap workFuel finalFuel uv fragment childAfter finished observedFinish
            have canonicalLater := finalAt workFuel
            rw [Nat.add_comm workFuel finalFuel] at observedLater
            have sameCache : canonicalAfter = finished :=
              Option.some.inj (canonicalLater.symm.trans observedLater)
            subst canonicalAfter
            let entry := advance seed (limit * (bound + own + 1))
            let retained := ceiling + limit * (bound + own)
            have entryFits : Fits entry.2 caller.checked := fits.mono
              (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed (limit * (bound + own + 1)))
            have entryKnown : Heap (fun guard => guard ∈ entry.1) caller.checked.native.machine.heap :=
              fun key edge found => SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge
                seed (limit * (bound + own + 1)) (known key edge found)
            have entryReserved : eagerReserved bits recursiveDepth entry retained :=
              tupleReserved_first_callback bits limit own height limit (bound + own) ceiling
                continuation admitted seed reserved
            have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass (Nat.le_trans childMass (Nat.le_add_right _ _))
            have callback := identity_callback_emitted_complete_at_any_budget graph checkEmpty edgesOf
              formulas solver recursiveDepth recursive next caller final finished metadata uv fragment entry retained
              finishedPacket entryFits entryKnown selectionMembers selectionLength actualMass entryReserved workFuel
            rw [querySame] at callback
            have included := first_callback_le_tuple_of_growth limit own height limit (bound + own) ceiling
              continuation growth seed
            have enlarged := identity_emitted_complete_mono included.1 included.2 callback
            have actualHook : IdentityEmittedCompleteResources formulas solver caller plan
                (hook fragment caller memos.query finished) := by
              simpa only [hook, visit] using enlarged
            cases observedHook : hook fragment caller memos.query finished with
            | complete outputs reached saved =>
                simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish] using actualHook
            | stopped outputs reason endpoint =>
                simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish,
                  IdentityEmittedCompleteResources, emitted] using actualHook
  · rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
    simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
      SourcePruningEnumerationCachedOwn.prepare, allowed]
    constructor
    · intro output member
      cases member
    · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
      intro output member
      cases member

end ActualIdentityEmptyPreparedTuple
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualIdentityFallbackConsEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
local notation "Hook" => Fragment → Caller (bits + 2) → Queries → Cached →
  NativeContinuations.HookResult (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)

/-- Record actual captured closures and actual completed fallback-head events. -/
private inductive IdentityActualTupleContext
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat) :
    List Fragment → List (Node × List Suspended) → Caller (bits + 2) → Cached → Queries →
      Seed → Nat → Done → Stopped → Prop where
  | captured (hook : Hook)
      (source : hook = SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (Typing := Unit) (width := bits + 2)
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
          none (fun _ _ => none) workFuel recursiveDepth)
        graph [] none (fun _ _ => none) workFuel metadata uv)
      (prepared : SourcePruningEnumerationCachedOwn.prepare capturedCaller.checked.native.machine.heap
        scs edge capturedBefore = some [((edge.entry.key.symbol, staged, residual), capturedOwn)]) :
      IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        [] (staged.map (fun input => (input.1, input.2.1))) capturedCaller capturedOwn capturedQueries
        initialSeed initialMass
        (fun fragments reached saved after =>
          let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
          let middle := SelectedEdge.finish residual fragment after
          match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel uv fragment middle with
          | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook capturedCaller capturedQueries
              (some (.complete fragment reached saved finished))
          | none => SourcePruningEnumerationSharedReceiptContinuation.run hook capturedCaller capturedQueries
              (some (.finalizeStopped fragment reached saved middle)))
        (fun completed observation candidate => SourcePruningEnumerationSharedReceiptContinuation.run
          hook capturedCaller capturedQueries (some (.stopped completed observation candidate)))
  | fallbackTail {completedPrefix caller before queries seed mass done stopped bucket incoming rest
        fragment returned reached saved after outer waiting}
      (origin : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        completedPrefix ((incoming, bucket) :: rest) caller before queries seed mass done stopped)
      (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false)
    (observed : ChildDispatch.run checkEmpty workFuel workFuel workFuel workFuel workFuel
        bucket incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some after)) :
      IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        (completedPrefix ++ [fragment]) rest reached after saved (advance seed (bucket.length + 1))
        (mass + bucket.length) (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed))

  | ordinaryEmptyTail {completedPrefix caller before queries seed mass done stopped bucket rest
        parentEntry rows depth free selectedRow alternatives rowResidual rowOwn}
      (origin : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        completedPrefix ((.node parentEntry rows depth free, bucket) :: rest)
        caller before queries seed mass done stopped)
      (ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket
        (.node parentEntry rows depth free) = true)
      (first : edgesOf (.node parentEntry rows depth free) = selectedRow :: alternatives)
      (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket
        selectedRow before = some [((selectedRow.entry.key.symbol, [], rowResidual), rowOwn)]) :
      IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        (completedPrefix ++ [.node selectedRow.entry.key.symbol []]) rest caller
        (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn)
        queries seed mass (fun fragments => done (.node selectedRow.entry.key.symbol [] :: fragments))
        (fun completed => stopped (.node selectedRow.entry.key.symbol [] :: completed))

/-- The pointwise context target derives prefix packets and real closed callback resources. -/
private def IdentityActualTupleAt
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (limit own height count bound : Nat) : Prop :=
  IdentityEagerEmittedCompleteAtDepth (bits := bits) graph checkEmpty edgesOf formulas solver recursiveDepth →
  ∀ (inventory : Inventory) (memos : Memos) (handle : Nat),
    memos.query = capturedQueries →
    Packet formulas solver inventory capturedCaller memos metadata capturedBefore →
    EnumerationDriver.Ready uv capturedBefore.core →
    capturedBefore.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv capturedBefore.core →
    Fits initialSeed.2 capturedCaller.checked →
    Heap (fun guard => guard ∈ initialSeed.1) capturedCaller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound capturedOwn.core ≤ initialMass →
    staged.length ≤ count →
    (∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      Available capturedCaller.checked.native.machine.heap child ∧ child.free = [] ∧
      MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
      (∀ sc ∈ bucket, sc.var < capturedOwn.core.counter) ∧ InputsPending capturedOwn.core bucket) →
    tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound initialMass (fun retained current => eagerFinal recursiveDepth current retained)
      (fun retained current => eagerReserved bits recursiveDepth current retained) initialSeed →
    ∀ completedPrefix inputs caller before queries seed mass done stopped,
      IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        completedPrefix inputs caller before queries seed mass done stopped →
      (TupleInputs formulas solver capturedCaller metadata capturedOwn
          (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before ∧
        Fits seed.2 caller.checked ∧
        Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ mass) ∧
      (inputs = [] → IdentityEmittedCompleteResources formulas solver capturedCaller
        (tuplePlan (nodePlan limit own height) count bound initialMass
          (fun retained current => eagerFinal recursiveDepth current retained) initialSeed)
        (SourcePruningEnumerationSharedPreparedRecursive.finish uv (done [] caller queries before)))

/-- An actual fallback head derives the complete resource entry for its shorter tuple tail. -/
private theorem identity_fallback_cons_actual_entry
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Unit) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (bucket : List Suspended) (incoming : Node) (rest : List (Node × List Suspended))
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 caller.checked) (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false)
    (restGenuine : ∀ child retained, (child, retained) ∈ rest →
      Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained)
    (workFuel : Nat) (fragment : Fragment) (returned outer : Core)
    (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (waiting : EnumerationWaitingIndex.Waiting)
    (graph : Graph Symbol Constraint) (recursiveDepth uv : Nat)
    (capturedCaller : Caller (bits + 2)) (capturedQueries : Queries) (capturedBefore : Cached)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
    (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat) (completedPrefix : List Fragment) (currentMass : Nat)
    (done : Done) (stopped : Stopped)
    (contextOrigin : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix ((incoming, bucket) :: rest) caller before memos.query seed currentMass done stopped)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ currentMass)
    (observed : ChildDispatch.run checkEmpty workFuel workFuel workFuel workFuel workFuel
      bucket incoming caller before memos.query =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some after)) :
    ChildInputs formulas solver caller metadata before bucket fragment reached saved after ∧
      Fits (advance seed (bucket.length + 1)).2 reached.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) reached.checked.native.machine.heap ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core + bucket.length ∧
      (∀ child retained, (child, retained) ∈ rest →
        Available reached.checked.native.machine.heap child ∧ child.free = [] ∧
        (∀ sc ∈ retained, sc.var < after.core.counter) ∧ InputsPending after.core retained) ∧
      (∀ fragments finalCaller queries finished,
        TupleInputs formulas solver reached metadata after rest fragments finalCaller queries finished →
        TupleInputs formulas solver caller metadata before ((incoming, bucket) :: rest)
          (fragment :: fragments) finalCaller queries finished) ∧
        SourcePruningEnumerationSharedChildVisitors.visitChildren
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf)
          done stopped ((incoming, bucket) :: rest) caller before memos.query =
        SourcePruningEnumerationSharedChildVisitors.visitChildren
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved ∧
      IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        (completedPrefix ++ [fragment]) rest reached after saved (advance seed (bucket.length + 1))
        (currentMass + bucket.length) (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ currentMass + bucket.length := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨final, next, afterRoots, _later, post, query, growth, afterPaths, storage,
      afterRealized, afterCounts, afterFlags, origin, protects, references, pendingAfter,
      shape, actualFits, actualKnown⟩ :=
    ChildDispatch.observed_complete_with_fragments_resources seed formulas solver inventory caller before
      checkEmpty bucket incoming roots memos packet.context packet.safe paths counts flags realized
      bounded pending available closed fits reserved known workFuel workFuel workFuel workFuel workFuel
      [.ok (fragment, returned)] reached after saved outer waiting observed (.inr ⟨fragment, returned, rfl⟩)
  rcases shape with rejected | ⟨produced, singleton, afterSafe, fragmentBound, fragmentPending, fragmentAvoid⟩
  · cases rejected
  · have pairSame : (fragment, returned) = (produced, after.core) :=
      Except.ok.inj (List.cons.inj singleton).1
    have fragmentSame : fragment = produced := congrArg Prod.fst pairSame
    subst produced
    have protectsEnumerated (held : Nat) (old : Fragment)
        (stored : before.core.values[held]? = some (.enumerated old)) :
        EnumerationDriver.Protected held before.core after.core := by
      obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held old stored
      exact protects held inside root (pending held old stored)
    have afterPacket : Packet formulas solver next reached final metadata after := by
      refine ⟨post.context, afterSafe, pendingAfter packet.pending,
        ⟨afterRoots, afterPaths, storage, afterRealized, afterCounts, afterFlags⟩, ?_, ?_⟩
      · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
        obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core after.core
          afterSafe level frontier oldOrder origin protectsEnumerated
        exact ⟨nextLevel, frontier, afterOrder⟩
      · intro group member entry listed
        exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
    have head : ChildInputs formulas solver caller metadata before bucket fragment reached saved after :=
      ⟨next, final, post, query, afterPacket, growth, origin, protects,
        (fun allowed valid supplied _future => references allowed valid supplied),
        fragmentBound, fragmentPending, fragmentAvoid⟩
    have genuine : ∀ child retained, (child, retained) ∈ (incoming, bucket) :: rest →
        Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
        (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained := by
      intro child retained member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact ⟨available, closed, bounded, pending⟩
      · exact restGenuine child retained member
    have combined := child_then_tuple_inputs formulas solver inventory caller memos metadata before
      incoming bucket rest packet genuine fragment reached saved after head
    have actualMass := ChildDispatch.observed_scalar_bounds checkEmpty
      workFuel workFuel workFuel workFuel workFuel bucket incoming caller before memos.query after
      (congrArg Prod.snd observed)
    refine ⟨head, actualFits, actualKnown, actualMass.2, combined.1, combined.2, ?_,
      IdentityActualTupleContext.fallbackTail contextOrigin fallback observed,
      Nat.le_trans actualMass.2 (Nat.add_le_add_right mass bucket.length)⟩
    simp only [SourcePruningEnumerationSharedChildVisitors.visitChildren]
    rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty
      workFuel workFuel workFuel workFuel workFuel edgesOf bucket incoming caller before memos.query
      _ _ fallback]
    simp only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, observed]

end ActualIdentityFallbackConsEntry
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualIdentityOrdinaryEmptyEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The first empty ordinary row derives the actual consumeSelected entry and parent tuple tail. -/
private theorem identity_ordinary_empty_row_actual_entry
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat)
    (completedPrefix : List Fragment) (done : Done) (stopped : Stopped)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (bucket : List Suspended) (rest : List (Node × List Suspended)) (seed : Seed) (mass : Nat)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (selectedRow : EdgeValue Symbol Constraint) (alternatives : List (EdgeValue Symbol Constraint))
    (rowTries : List EqualityTrie.Trie) (rowResidual : Option Constraint)
    (contextOrigin : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix (((.node parentEntry rows depth free), bucket) :: rest) caller before memos.query seed mass done stopped)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
    (available : Available caller.checked.native.machine.heap (.node parentEntry rows depth free)) (closed : free = [])
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ mass)
    (restGenuine : ∀ child retained, (child, retained) ∈ rest →
      Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained)
    (ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket (.node parentEntry rows depth free) = true)
    (first : edgesOf (.node parentEntry rows depth free) = selectedRow :: alternatives)
    (selectionMembers : ∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows)
    (empty : selectedRow.children = [])
    (allowed : arityAllows selectedRow.children.length bucket = true)
    (projected : SourcePruningEnumerationConstraint.project selectedRow.entry.key.constraint =
      some (rowTries, rowResidual)) :
    ∃ rowOwn : Cached,
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket selectedRow before =
        some [((selectedRow.entry.key.symbol, [], rowResidual), rowOwn)] ∧
      ChildInputs formulas solver caller metadata before bucket (.node selectedRow.entry.key.symbol []) caller memos.query (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn) ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn).core ≤ mass ∧
      (∀ child retained, (child, retained) ∈ rest →
        Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
        (∀ sc ∈ retained, sc.var < (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn).core.counter) ∧ InputsPending (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn).core retained) ∧
      (SourcePruningEnumerationSharedChildVisitors.visitSelected
        (fun bucket child current cache queries yes no =>
          if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free) then
            SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              workFuel workFuel workFuel workFuel workFuel edgesOf bucket child current cache queries yes no
          else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty
            workFuel workFuel workFuel workFuel workFuel bucket child current cache queries yes no)
        (SourcePruningEnumerationSharedEagerChildren.consumeSelected (fun fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved) caller memos.query)
        bucket selectedRow caller before memos.query =
        SourcePruningEnumerationSharedEagerChildren.consumeSelected (fun fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved) caller memos.query
        (.complete (.node selectedRow.entry.key.symbol []) caller memos.query (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn))) ∧
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        workFuel workFuel workFuel workFuel workFuel edgesOf bucket (.node parentEntry rows depth free)
        caller before memos.query (fun fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved) (fun observation candidate => stopped [] observation candidate) =
        SourcePruningEnumerationSharedBranching.scan
          (fun row reached saved captured => SourcePruningEnumerationSharedChildVisitors.visitSelected
            (fun bucket child current cache queries yes no =>
          if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free) then
            SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              workFuel workFuel workFuel workFuel workFuel edgesOf bucket child current cache queries yes no
          else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty
            workFuel workFuel workFuel workFuel workFuel bucket child current cache queries yes no)
            (SourcePruningEnumerationSharedEagerChildren.consumeSelected (fun fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved) reached saved)
            bucket row reached captured saved)
          before (selectedRow :: alternatives) caller memos.query) ∧
      IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
        (completedPrefix ++ [(.node selectedRow.entry.key.symbol [])]) rest caller (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn)
        memos.query seed mass (fun fragments => done ((.node selectedRow.entry.key.symbol []) :: fragments))
        (fun completed => stopped ((.node selectedRow.entry.key.symbol []) :: completed)) := by
  have selected : selectedRow ∈ rows := selectionMembers parentEntry rows depth free selectedRow (by rw [first]; simp)
  obtain ⟨_roots, _action, rowOwn, _paths, ownReceipt, ownPacket, ownMass, _lower, reducing⟩ :=
    ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
      selectedRow bucket packet available closed selected bounded pending allowed rowTries rowResidual projected
  obtain ⟨_prepared, ownRun, _raw, ownCore, ownCounter, _ownForest, _ownSafe,
      _ownPaths, _ownRealized, _ownCounts, _ownFlags, _combinedPending, _genuine, ownProtects⟩ := ownReceipt
  have nilInputs : SourcePruningEnumerationEdgeInputs.children selectedRow bucket before.core.counter rowTries = [] := by
    simp [SourcePruningEnumerationEdgeInputs.children, empty]
  have prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket selectedRow before =
      some [((selectedRow.entry.key.symbol, [], rowResidual), rowOwn)] := by
    simpa only [nilInputs, List.map_nil] using ownRun
  have history : TupleInputs formulas solver caller metadata rowOwn
      (SourcePruningEnumerationEdgeInputs.children selectedRow bucket before.core.counter rowTries)
      [] caller memos.query rowOwn := by
    rw [nilInputs]
    exact tuple_inputs_nil formulas solver inventory caller memos metadata rowOwn ownPacket
  have head := own_tuple_child_inputs formulas solver caller metadata before rowOwn selectedRow bucket
    rowTries rowResidual ownCore ownCounter ownProtects [] caller memos.query rowOwn history
  have genuine : ∀ child retained, (child, retained) ∈ ((.node parentEntry rows depth free), bucket) :: rest →
      Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained := by
    intro child retained member
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨available, closed, bounded, pending⟩
    · exact restGenuine child retained member
  have combined := child_then_tuple_inputs formulas solver inventory caller memos metadata before
    (.node parentEntry rows depth free) bucket rest packet genuine (.node selectedRow.entry.key.symbol []) caller memos.query (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn) head
  have afterMass : SourcePruningEnumerationPrefixAdmission.suspendedBound (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn).core ≤ mass := by
    change SourcePruningEnumerationPrefixAdmission.suspendedBound rowOwn.core ≤ mass
    rw [ownMass]
    exact currentMass
  refine ⟨rowOwn, prepared, head, fits, known, afterMass, combined.1, ?_, ?_,
    IdentityActualTupleContext.ordinaryEmptyTail contextOrigin ordinary first prepared⟩
  · rw [reducing, nilInputs]
    rfl
  · rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary checkEmpty
      workFuel workFuel workFuel workFuel workFuel edgesOf bucket (.node parentEntry rows depth free)
      caller before memos.query _ _ ordinary, first]

end ActualIdentityOrdinaryEmptyEntry
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualTuplePrefixExtension
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Extend the completed tuple prefix through its actual next child resources. -/
private theorem tuple_inputs_extend_current_head
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (before : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller : Caller (bits + 2)) (queries : Queries) (current : Cached)
    (incoming : Node) (bucket : List Suspended) (fragment : Fragment)
    (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (previous : TupleInputs formulas solver original metadata before inputs completed caller queries current)
    (member : (incoming, bucket) ∈ inputs)
    (pending : InputsPending current.core bucket)
    (head : ChildInputs formulas solver caller metadata current bucket fragment reached saved after) :
    TupleInputs formulas solver original metadata before inputs
      (completed ++ [fragment]) reached saved after := by
  obtain ⟨_currentInventory, _currentMemos, previousPost, _previousQuery, currentPacket,
    previousGrowth, previousOrigin, previousProtected, previousRootsProtected,
    previousReferences, previousBounds, previousHistory⟩ := previous
  obtain ⟨next, final, headPost, query, afterPacket, growth, origin, protects,
    references, fragmentBound, fragmentPending, fragmentSeparate⟩ := head
  have protectsEnumerated (held : Nat) (old : Fragment)
      (stored : current.core.values[held]? = some (.enumerated old)) :
      EnumerationDriver.Protected held current.core after.core := by
    obtain ⟨inside, root⟩ := enumerated_root current.core currentPacket.safe held old stored
    exact protects held inside root (pending held old stored)
  have protectsOriginalRoot (held : Nat) (inside : held < before.core.counter)
      (root : IsRoot before.core.representatives held)
      (avoids : ∀ child retained, (child, retained) ∈ inputs →
        Avoids before.core.representatives held retained) :
      EnumerationDriver.Protected held current.core after.core := by
    have first := previousRootsProtected held inside root avoids
    exact protects held (Nat.lt_of_lt_of_le inside previousGrowth) first.root
      (first.avoids bucket (avoids incoming bucket member))
  refine ⟨next, final, previousPost.trans headPost, query, afterPacket,
    Nat.le_trans previousGrowth growth, previousOrigin.trans origin, ?_, ?_, ?_, ?_, ?_⟩
  · intro held old stored
    have first := previousProtected held old stored
    exact first.trans (protectsEnumerated held old (first.value.trans stored))
  · intro held inside root avoids
    exact (previousRootsProtected held inside root avoids).trans
      (protectsOriginalRoot held inside root avoids)
  · intro allowed valid supplied future
    apply references allowed (previousReferences allowed valid supplied future)
      (supplied incoming bucket member)
    intro held inside
    exact future held (Nat.le_trans previousGrowth inside)
  · intro child included
    rcases List.mem_append.mp included with earlier | latest
    · exact fragmentBound_mono _ _ growth child (previousBounds child earlier)
    · rcases List.mem_singleton.mp latest with rfl
      exact fragmentBound
  · intro child included
    rcases List.mem_append.mp included with earlier | latest
    · obtain ⟨childPending, childSeparate⟩ := previousHistory child earlier
      refine ⟨pendingFragment_preserved current.core after.core currentPacket.safe afterPacket.safe
        growth child (previousBounds child earlier) childPending origin protectsEnumerated, ?_⟩
      intro held inside root avoids
      have lastProtection := protectsOriginalRoot held inside root avoids
      exact (fragmentAvoid_classes current.core.representatives after.core.representatives
        held child lastProtection.classes).mpr (childSeparate held inside root avoids)
    · rcases List.mem_singleton.mp latest with rfl
      refine ⟨fragmentPending, ?_⟩
      intro held inside root avoids
      have first := previousRootsProtected held inside root avoids
      exact fragmentSeparate held (Nat.lt_of_lt_of_le inside previousGrowth) first.root
        (first.avoids bucket (avoids incoming bucket member))

end ActualTuplePrefixExtension
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualTuplePrefixReservation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedIncomingReservation (Seed advance advance_add Reserved)

/-- The original tuple reservation covers its complete ordered native fallback schedule. -/
private theorem tupleReserved_fallback_native_schedule (bits limit own height count bound ceiling : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound ceiling continuation admitted seed) :
    Reserved bits seed (count * (bound + 1)) := by
  induction count generalizing ceiling seed with
  | zero =>
      simpa only [Nat.zero_mul] using
        SourcePruningEnumerationSharedIncomingReservation.reserved_zero bits seed
  | succ count ih =>
      let tail := fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current
      let covered := fun retained current => tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
        count bound retained continuation admitted current
      have child : nodeReserved bits limit own height bound ceiling tail covered seed := reserved
      have fallback := nodeReserved_fallback bits limit own height bound ceiling tail covered seed child
      have later := ih (ceiling + bound) (advance seed (bound + 1)) fallback.2
      intro index less
      by_cases first : index < bound + 1
      · exact fallback.1 index first
      · have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by
          rw [Nat.succ_mul]
          omega
        have remaining : index - (bound + 1) < count * (bound + 1) := by
          rw [counts] at less
          omega
        have room := later (index - (bound + 1)) remaining
        have offset : (bound + 1) + (index - (bound + 1)) = index := by omega
        simpa only [← advance_add, offset] using room

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (SourcePruningEnumerationSharedPreparedRecursive.Output (bits + 2) Unit)
  (SourcePruningEnumerationSharedPreparedRecursive.Failure (bits + 2) Unit) (bits + 2)
local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual captured, fallback and empty-row contexts retain one bounded native schedule. -/
private theorem identity_actual_tuple_prefix_costs
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass bound : Nat)
    (bounded : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      bucket.length ≤ bound)
    (completedPrefix : List Fragment) (inputs : List (Node × List Suspended))
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (seed : Seed) (mass : Nat) (done : Done) (stopped : Stopped)
    (context : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix inputs caller before queries seed mass done stopped) :
    ∃ consumed,
      seed = advance initialSeed consumed ∧
      consumed ≤ completedPrefix.length * (bound + 1) ∧
      mass ≤ initialMass + completedPrefix.length * bound ∧
      completedPrefix.length + inputs.length = staged.length ∧
      (∀ input ∈ inputs, input ∈ staged.map (fun item => (item.1, item.2.1))) := by
  induction context with
  | captured _hook _source _prepared =>
      refine ⟨0, rfl, Nat.zero_le _, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro input member
        exact member
  | @fallbackTail completedPrefix _caller _before _queries _seed _mass _done _stopped
      bucket incoming _rest _fragment _returned _reached _saved _after _outer _waiting
      _origin _fallback _observed ih =>
      obtain ⟨consumed, seedAt, paid, retainedMass, lengths, members⟩ := ih
      have bucketBound : bucket.length ≤ bound := bounded incoming bucket (members _ (by simp))
      refine ⟨consumed + (bucket.length + 1), ?_, ?_, ?_, ?_, ?_⟩
      · rw [seedAt, ← advance_add]
      · simp only [List.length_append, List.length_singleton]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [List.length_append, List.length_singleton]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [List.length_cons] at lengths
        simp only [List.length_append, List.length_singleton]
        omega
      · intro input member
        exact members input (List.mem_cons_of_mem _ member)
  | @ordinaryEmptyTail completedPrefix _caller _before _queries _seed _mass _done _stopped
      _bucket _rest _parentEntry _rows _depth _free _selectedRow _alternatives _rowResidual _rowOwn
      _origin _ordinary _first _prepared ih =>
      obtain ⟨consumed, seedAt, paid, retainedMass, lengths, members⟩ := ih
      refine ⟨consumed, seedAt, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [List.length_append, List.length_singleton]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [List.length_cons] at lengths
        simp only [List.length_append, List.length_singleton]
        omega
      · intro input member
        exact members input (List.mem_cons_of_mem _ member)

/-- An actual fallback entry receives native admission from the original tuple reservation. -/
private theorem identity_actual_fallback_native_reservation
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass limit own height count bound : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (bounded : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      bucket.length ≤ bound)
    (counted : staged.length ≤ count)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound initialMass continuation admitted initialSeed)
    (completedPrefix : List Fragment) (incoming : Node) (bucket : List Suspended)
    (rest : List (Node × List Suspended)) (caller : Caller (bits + 2))
    (before : Cached) (queries : Queries) (seed : Seed) (mass : Nat)
    (done : Done) (stopped : Stopped)
    (context : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix ((incoming, bucket) :: rest) caller before queries seed mass done stopped) :
    Reserved bits seed (bucket.length + 1) := by
  obtain ⟨consumed, seedAt, paid, _retainedMass, lengths, members⟩ :=
    identity_actual_tuple_prefix_costs graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed
      initialMass bound bounded completedPrefix ((incoming, bucket) :: rest) caller before queries
      seed mass done stopped context
  have bucketBound : bucket.length ≤ bound := bounded incoming bucket (members _ (by simp))
  have currentCount : completedPrefix.length + 1 ≤ count := by
    simp only [List.length_cons] at lengths
    omega
  have coverage := Nat.mul_le_mul_right (bound + 1) currentCount
  rw [Nat.add_mul, Nat.one_mul] at coverage
  have schedule := tupleReserved_fallback_native_schedule bits limit own height count bound initialMass
    continuation admitted initialSeed reserved
  have remaining : Reserved bits initialSeed (consumed + (bucket.length + 1)) :=
    schedule.prefix (by omega)
  rw [seedAt]
  exact remaining.after_prefix

end ActualTuplePrefixReservation
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualCapturedPrefixEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual captured own receipt derives its Packet and empty completed prefix. -/
private theorem identity_captured_actual_prefix_entry
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Unit) (before : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (own : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (packet : Packet formulas solver inventory caller memos metadata before)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), own)]) :
    Packet formulas solver inventory caller memos metadata own ∧
      TupleInputs formulas solver caller metadata own
        (staged.map (fun input => (input.1, input.2.1))) [] caller memos.query own := by
  have ownPacket : Packet formulas solver inventory caller memos metadata own := by
    obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
    have complete := SourcePruningEnumerationCachedOwn.complete caller.checked.native.machine.heap
      before scs edge roots storage realized paths counts flags
    by_cases allowed : arityAllows edge.children.length scs = true
    · simp only [allowed, ↓reduceIte] at complete
      cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none =>
          simp only [projected] at complete
          have impossible := complete.1.symm.trans prepared
          cases impossible
      | some pair =>
          obtain ⟨tries, projectedResidual⟩ := pair
          simp only [projected] at complete
          obtain ⟨_action, candidate, _prefix, actual, _raw, ownCore, ownCounter, _aligned,
            _forest, ownPaths, ownStorage, ownRealized, ownCounts, _waiting, _expandable, ownFlags⟩ := complete
          have endpointSame : candidate = own :=
            congrArg Prod.snd (List.cons.inj (Option.some.inj (actual.symm.trans prepared))).1
          subst candidate
          have ownSafe : Safe own.core := by
            rw [ownCore]
            exact suspension_safe tries.length before.core packet.safe
          have origin : EnumeratedOrigin before.core own.core := by
            rw [ownCore]
            exact suspension_origin tries.length before.core
          have protects (held : Nat) (inside : held < before.core.counter)
              (root : IsRoot before.core.representatives held) :
              EnumerationDriver.Protected held before.core own.core := by
            rw [ownCore]
            exact EnumerationDriver.suspension_protected held tries.length before.core packet.safe inside root
          have protectsEnumerated (held : Nat) (fragment : Fragment)
              (stored : before.core.values[held]? = some (.enumerated fragment)) :
              EnumerationDriver.Protected held before.core own.core := by
            obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held fragment stored
            exact protects held inside root
          have afterPending : EnumerationReferences.PendingReferences own.core := by
            intro held fragment stored
            have previous := origin held fragment stored
            have incoming : EnumerationReferences.ReferencesAllowed
                (fun uv => ¬UnionFind.SameClass before.core.representatives held uv) own.core := by
              rw [ownCore]
              exact EnumerationReferences.suspension_allowed _ tries.length before.core
                (packet.pending held fragment previous)
            intro value member sc listed related
            exact incoming value member sc listed
              (((protectsEnumerated held fragment previous).classes sc.var).mp related)
          have growth : before.core.counter ≤ own.core.counter := by rw [ownCounter]; omega
          refine ⟨packet.context, ownSafe, afterPending,
            ⟨roots, ownPaths, ownStorage, ownRealized, ownCounts, ownFlags⟩, ?_, ?_⟩
          · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
            obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core own.core
              ownSafe level frontier oldOrder origin protectsEnumerated
            exact ⟨nextLevel, frontier, afterOrder⟩
          · intro group member entry listed
            exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
    · simp only [allowed] at complete
      have impossible := Option.some.inj (complete.1.symm.trans prepared)
      cases impossible
  refine ⟨ownPacket, inventory, memos, Post.refl ownPacket.context, rfl, ownPacket,
    Nat.le_refl _, .refl _, ?_, ?_, (fun _ valid _ _ => valid), ?_, ?_⟩
  · intro held fragment stored
    exact EnumerationDriver.Protected.refl held own.core (enumerated_root own.core ownPacket.safe held fragment stored).2
  · intro held _ root _
    exact EnumerationDriver.Protected.refl held own.core root
  · intro fragment member
    cases member
  · intro fragment member
    cases member

end ActualCapturedPrefixEntry
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualTupleInputTransport
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A completed prefix retains every original tuple input at its current endpoint. -/
private theorem tuple_inputs_current_inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (before : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller : Caller (bits + 2)) (queries : Queries) (current : Cached)
    (previous : TupleInputs formulas solver original metadata before inputs completed caller queries current)
    (genuine : ∀ child bucket, (child, bucket) ∈ inputs →
      Available original.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) :
    ∀ child bucket, (child, bucket) ∈ inputs →
      Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ bucket, sc.var < current.core.counter) ∧ InputsPending current.core bucket := by
  obtain ⟨_next, _final, post, _query, _packet, growth, origin, protects,
    _rootProtection, _references, _bounds, _history⟩ := previous
  intro child bucket member
  obtain ⟨available, closed, bounded, pending⟩ := genuine child bucket member
  refine ⟨post.effects.keeps.available child available, closed,
    fun sc included => Nat.lt_of_lt_of_le (bounded sc included) growth, ?_⟩
  intro held fragment stored
  have originalStored := origin held fragment stored
  exact (protects held fragment originalStored).avoids bucket
    (pending held fragment originalStored)

end ActualTupleInputTransport
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualContextPrefixResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (SourcePruningEnumerationSharedPreparedRecursive.Output (bits + 2) Unit)
  (SourcePruningEnumerationSharedPreparedRecursive.Failure (bits + 2) Unit) (bits + 2)
local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- An actual empty staged receipt identifies accepted arity, projection and empty children. -/
private theorem identity_observed_empty_own_shape
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Unit) (before : Cached) (bucket : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (own : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket edge before =
      some [((edge.entry.key.symbol, [], residual), own)]) :
    ∃ tries : List EqualityTrie.Trie,
      arityAllows edge.children.length bucket = true ∧
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      edge.children = [] := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  have complete := SourcePruningEnumerationCachedOwn.complete caller.checked.native.machine.heap
    before bucket edge roots storage realized paths counts flags
  by_cases allowed : arityAllows edge.children.length bucket = true
  · simp only [allowed, ↓reduceIte] at complete
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [projected] at complete
        have impossible := complete.1.symm.trans prepared
        cases impossible
    | some pair =>
        obtain ⟨tries, projectedResidual⟩ := pair
        simp only [projected] at complete
        obtain ⟨_action, _candidate, _prefix, actual, _rest⟩ := complete
        have same := (List.cons.inj (Option.some.inj (actual.symm.trans prepared))).1
        have contentsSame := congrArg Prod.fst same
        have tailSame := congrArg Prod.snd contentsSame
        have residualSame : projectedResidual = residual := congrArg Prod.snd tailSame
        have stagedSame := congrArg Prod.fst tailSame
        refine ⟨tries, allowed, ?_, ?_⟩
        · exact congrArg (fun replacement => some (tries, replacement)) residualSame
        · have measured := congrArg List.length stagedSame
          have emptyLength : edge.children.length = 0 := by
            simpa only [List.length_map, List.length_zipIdx, List.length_nil] using measured
          revert emptyLength
          cases edge.children with
          | nil => intro _zero; rfl
          | cons _child _rest =>
              intro impossible
              simp only [List.length_cons] at impossible
              omega
  · simp only [allowed] at complete
    have impossible := Option.some.inj (complete.1.symm.trans prepared)
    cases impossible

/-- Each actual context derives its full completed-prefix resources and remaining input validity. -/
private theorem identity_actual_context_prefix_resources
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (limit own height count bound : Nat)
    (_workerIH : IdentityEagerEmittedCompleteAtDepth (bits := bits) graph checkEmpty edgesOf formulas solver recursiveDepth)
    (initialInventory : Inventory) (initialMemos : Memos) (handle : Nat)
    (initialQuery : initialMemos.query = capturedQueries)
    (initialPacket : Packet formulas solver initialInventory capturedCaller initialMemos metadata capturedBefore)
    (_ready : EnumerationDriver.Ready uv capturedBefore.core)
    (_stored : capturedBefore.core.values[uv]? = some (.unenumerated (some handle) scs))
    (_incoming : EnumerationReferences.IncomingAvoid uv capturedBefore.core)
    (initialFits : Fits initialSeed.2 capturedCaller.checked)
    (initialKnown : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ initialSeed.1)
      capturedCaller.checked.native.machine.heap)
    (initialMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound capturedOwn.core ≤ initialMass)
    (counted : staged.length ≤ count)
    (selectorMembers : ∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows)
    (_selectorLengths : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (genuine : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      Available capturedCaller.checked.native.machine.heap child ∧ child.free = [] ∧
      MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
      (∀ sc ∈ bucket, sc.var < capturedOwn.core.counter) ∧ InputsPending capturedOwn.core bucket)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound initialMass (fun retained current => eagerFinal recursiveDepth current retained)
      (fun retained current => eagerReserved bits recursiveDepth current retained) initialSeed)
    (completedPrefix : List Fragment) (inputs : List (Node × List Suspended))
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (seed : Seed) (mass : Nat) (done : Done) (stopped : Stopped)
    (context : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix inputs caller before queries seed mass done stopped) :
    TupleInputs formulas solver capturedCaller metadata capturedOwn
        (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before ∧
      Fits seed.2 caller.checked ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ mass ∧
      (∀ child bucket, (child, bucket) ∈ inputs →
        Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
        MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
        (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) ∧
      (∃ (currentInventory : Inventory) (currentMemos : Memos),
        currentMemos.query = queries ∧ Packet formulas solver currentInventory caller currentMemos metadata before) := by
  have originalInputs : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      Available capturedCaller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ bucket, sc.var < capturedOwn.core.counter) ∧ InputsPending capturedOwn.core bucket := by
    intro child bucket member
    have actual := genuine child bucket member
    exact ⟨actual.1, actual.2.1, actual.2.2.2.2.1, actual.2.2.2.2.2⟩
  have originalBounds : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      bucket.length ≤ bound := fun child bucket member => (genuine child bucket member).2.2.2.1
  have core : TupleInputs formulas solver capturedCaller metadata capturedOwn
        (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before ∧
      Fits seed.2 caller.checked ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ mass := by
    induction context with
    | captured _hook _source prepared =>
        obtain ⟨_ownPacket, emptyPrefix⟩ := identity_captured_actual_prefix_entry formulas solver
          initialInventory capturedCaller initialMemos metadata capturedBefore scs edge residual capturedOwn staged
          initialPacket prepared
        refine ⟨?_, initialFits, initialKnown, initialMassBound⟩
        simpa only [initialQuery] using emptyPrefix
    | @fallbackTail completedPrefix caller before queries seed mass done stopped bucket incoming rest
        fragment returned reached saved after outer waiting origin fallback observed ih =>
        obtain ⟨previous, fits, known, massBound⟩ := ih
        obtain ⟨_consumed, _seedAt, _paid, _retainedMass, _lengths, members⟩ :=
          identity_actual_tuple_prefix_costs graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
            capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed
            initialMass bound originalBounds completedPrefix ((incoming, bucket) :: rest) caller before queries
            seed mass done stopped origin
        have transported := tuple_inputs_current_inputs formulas solver capturedCaller metadata capturedOwn
          (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before previous originalInputs
        have currentGenuine : ∀ child retained, (child, retained) ∈ (incoming, bucket) :: rest →
            Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
            (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained := by
          intro child retained member
          exact transported child retained (members _ member)
        have headGenuine := currentGenuine incoming bucket (by simp)
        have member : (incoming, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) := members _ (by simp)
        have currentPacket : ∃ (currentInventory : Inventory) (currentMemos : Memos),
            currentMemos.query = queries ∧ Packet formulas solver currentInventory caller currentMemos metadata before := by
          obtain ⟨currentInventory, currentMemos, _post, query, packet, _rest⟩ := previous
          exact ⟨currentInventory, currentMemos, query, packet⟩
        obtain ⟨currentInventory, currentMemos, query, packet⟩ := currentPacket
        have originAtMemos : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
            capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
            completedPrefix ((incoming, bucket) :: rest) caller before currentMemos.query seed mass done stopped := by
          simpa only [query] using origin
        have observedAtMemos : ChildDispatch.run checkEmpty workFuel workFuel workFuel workFuel workFuel
            bucket incoming caller before currentMemos.query =
            ((.ok (some [.ok (fragment, returned)]), reached, saved, outer, waiting), some after) := by
          simpa only [query] using observed
        have native := identity_actual_fallback_native_reservation graph checkEmpty edgesOf recursiveDepth workFuel
          metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed
          initialMass limit own height count bound
          (fun retained current => eagerFinal recursiveDepth current retained)
          (fun retained current => eagerReserved bits recursiveDepth current retained)
          originalBounds counted reserved completedPrefix incoming bucket rest caller before queries seed mass done stopped origin
        obtain ⟨head, afterFits, afterKnown, _massGrowth, _remaining, _tailFrame, _source, _next, afterMass⟩ :=
          identity_fallback_cons_actual_entry seed formulas solver currentInventory caller currentMemos metadata before
            checkEmpty edgesOf bucket incoming rest packet headGenuine.2.2.1 headGenuine.2.2.2 headGenuine.1 headGenuine.2.1
            fits native known fallback (fun child retained included => currentGenuine child retained (List.mem_cons_of_mem _ included))
            workFuel fragment returned outer reached saved after waiting graph recursiveDepth uv capturedCaller capturedQueries
            capturedBefore scs edge residual capturedOwn staged initialSeed initialMass completedPrefix mass done stopped
            originAtMemos massBound observedAtMemos
        have combined := tuple_inputs_extend_current_head formulas solver capturedCaller metadata capturedOwn
          (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before incoming bucket fragment
          reached saved after previous member headGenuine.2.2.2 head
        exact ⟨combined, afterFits, afterKnown, afterMass⟩
    | @ordinaryEmptyTail completedPrefix caller before queries seed mass done stopped bucket rest
        parentEntry rows depth free selectedRow alternatives rowResidual rowOwn origin ordinary first prepared ih =>
        obtain ⟨previous, fits, known, massBound⟩ := ih
        obtain ⟨_consumed, _seedAt, _paid, _retainedMass, _lengths, members⟩ :=
          identity_actual_tuple_prefix_costs graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
            capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed
            initialMass bound originalBounds completedPrefix ((.node parentEntry rows depth free, bucket) :: rest)
            caller before queries seed mass done stopped origin
        have transported := tuple_inputs_current_inputs formulas solver capturedCaller metadata capturedOwn
          (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before previous originalInputs
        have currentGenuine : ∀ child retained, (child, retained) ∈ (.node parentEntry rows depth free, bucket) :: rest →
            Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
            (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained := by
          intro child retained member
          exact transported child retained (members _ member)
        have headGenuine := currentGenuine (.node parentEntry rows depth free) bucket (by simp)
        have member : (.node parentEntry rows depth free, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) := members _ (by simp)
        have currentPacket : ∃ (currentInventory : Inventory) (currentMemos : Memos),
            currentMemos.query = queries ∧ Packet formulas solver currentInventory caller currentMemos metadata before := by
          obtain ⟨currentInventory, currentMemos, _post, query, packet, _rest⟩ := previous
          exact ⟨currentInventory, currentMemos, query, packet⟩
        obtain ⟨currentInventory, currentMemos, query, packet⟩ := currentPacket
        obtain ⟨tries, allowed, projected, empty⟩ := identity_observed_empty_own_shape formulas solver currentInventory
          caller currentMemos metadata before bucket selectedRow rowResidual rowOwn packet prepared
        have originAtMemos : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
            capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
            completedPrefix ((.node parentEntry rows depth free, bucket) :: rest) caller before currentMemos.query seed mass done stopped := by
          simpa only [query] using origin
        obtain ⟨generated, actual, head, afterFits, afterKnown, afterMass, _remaining, _selected, _scan, _next⟩ :=
          identity_ordinary_empty_row_actual_entry graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
            capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
            completedPrefix done stopped formulas solver currentInventory caller currentMemos before bucket rest seed mass
            parentEntry rows depth free selectedRow alternatives tries rowResidual originAtMemos packet
            headGenuine.2.2.1 headGenuine.2.2.2 headGenuine.1 headGenuine.2.1 fits known massBound
            (fun child retained included => currentGenuine child retained (List.mem_cons_of_mem _ included))
            ordinary first selectorMembers empty allowed projected
        have cacheSame : generated = rowOwn :=
          congrArg Prod.snd (List.cons.inj (Option.some.inj (actual.symm.trans prepared))).1
        subst generated
        have combined := tuple_inputs_extend_current_head formulas solver capturedCaller metadata capturedOwn
          (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before
          (.node parentEntry rows depth free) bucket (.node selectedRow.entry.key.symbol []) caller currentMemos.query
          (SelectedEdge.finish rowResidual (.node selectedRow.entry.key.symbol []) rowOwn) previous member headGenuine.2.2.2 head
        refine ⟨?_, afterFits, afterKnown, afterMass⟩
        simpa only [query] using combined
  obtain ⟨history, fits, known, massBound⟩ := core
  have transported := tuple_inputs_current_inputs formulas solver capturedCaller metadata capturedOwn
    (staged.map (fun input => (input.1, input.2.1))) completedPrefix caller queries before history originalInputs
  obtain ⟨_consumed, _seedAt, _paid, _retainedMass, _lengths, members⟩ :=
    identity_actual_tuple_prefix_costs graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed
      initialMass bound originalBounds completedPrefix inputs caller before queries seed mass done stopped context
  refine ⟨history, fits, known, massBound, ?_, ?_⟩
  · intro child bucket member
    have originalMember := members _ member
    have actual := transported child bucket originalMember
    have initial := genuine child bucket originalMember
    exact ⟨actual.1, actual.2.1, initial.2.2.1, initial.2.2.2.1, actual.2.2.1, actual.2.2.2⟩
  · obtain ⟨currentInventory, currentMemos, _post, query, packet, _rest⟩ := history
    exact ⟨currentInventory, currentMemos, query, packet⟩

end ActualContextPrefixResources
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualContextCallbackPlanning
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourceCurrentAllocatedNativeResourceForecast (Le)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (SourcePruningEnumerationSharedPreparedRecursive.Output (bits + 2) Unit)
  (SourcePruningEnumerationSharedPreparedRecursive.Failure (bits + 2) Unit) (bits + 2)
local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the captured own receipt and the exact actual done closure. -/
private theorem identity_actual_tuple_done_source
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat)
    (completedPrefix : List Fragment) (inputs : List (Node × List Suspended))
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (seed : Seed) (mass : Nat) (done : Done) (stopped : Stopped)
    (context : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix inputs caller before queries seed mass done stopped) :
    SourcePruningEnumerationCachedOwn.prepare capturedCaller.checked.native.machine.heap scs edge capturedBefore =
      some [((edge.entry.key.symbol, staged, residual), capturedOwn)] ∧
    ∀ (tail : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached),
      done tail reached saved after =
        let fragment : Fragment := .node edge.entry.key.symbol (completedPrefix ++ tail)
        let middle := SelectedEdge.finish residual fragment after
        SourcePruningEnumerationSharedReceiptContinuation.run
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
              (Typing := Unit) (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                workFuel workFuel workFuel workFuel workFuel edgesOf)
              (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
              none (fun _ _ => none) workFuel recursiveDepth)
            graph [] none (fun _ _ => none) workFuel metadata uv)
          capturedCaller capturedQueries
          (some (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
              workFuel uv fragment middle with
            | some finished => .complete fragment reached saved finished
            | none => .finalizeStopped fragment reached saved middle)) := by
  induction context with
  | captured hook source prepared =>
      refine ⟨prepared, ?_⟩
      intro tail reached saved after
      rw [source]
      cases observed : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel uv
        (.node edge.entry.key.symbol tail) (SelectedEdge.finish residual (.node edge.entry.key.symbol tail) after) <;>
          simp only [List.nil_append, observed]
  | @fallbackTail completedPrefix _caller _before _queries _seed _mass _done _stopped
      _bucket _incoming _rest fragment _returned _reached _saved _after _outer _waiting
      _origin _fallback _observed ih =>
      refine ⟨ih.1, ?_⟩
      intro tail reached saved after
      simpa only [List.append_assoc, List.singleton_append] using ih.2 (fragment :: tail) reached saved after
  | @ordinaryEmptyTail completedPrefix _caller _before _queries _seed _mass _done _stopped
      _bucket _rest _parentEntry _rows _depth _free selectedRow _alternatives _rowResidual _rowOwn
      _origin _ordinary _first _prepared ih =>
      refine ⟨ih.1, ?_⟩
      intro tail reached saved after
      simpa only [List.append_assoc, List.singleton_append] using
        ih.2 (.node selectedRow.entry.key.symbol [] :: tail) reached saved after

/-- An actual empty tail derives its callback padding, admission and enclosing forecast. -/
private theorem identity_actual_empty_tail_callback_plan
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass limit own height count bound : Nat)
    (bounded : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      bucket.length ≤ bound)
    (counted : staged.length ≤ count)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound initialMass (fun retained current => eagerFinal recursiveDepth current retained)
      (fun retained current => eagerReserved bits recursiveDepth current retained) initialSeed)
    (completedPrefix : List Fragment) (caller : Caller (bits + 2))
    (before : Cached) (queries : Queries) (seed : Seed) (mass : Nat) (done : Done) (stopped : Stopped)
    (context : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix [] caller before queries seed mass done stopped) :
    ∃ consumed,
      seed = advance initialSeed consumed ∧
      consumed ≤ count * (bound + 1) ∧
      mass ≤ initialMass + count * bound ∧
      eagerReserved bits recursiveDepth (advance initialSeed (count * (bound + 1)))
        (initialMass + count * bound) ∧
      Le (eagerFinal recursiveDepth (advance initialSeed (count * (bound + 1)))
          (initialMass + count * bound)).2
        (tuplePlan (nodePlan limit own height) count bound initialMass
          (fun retained current => eagerFinal recursiveDepth current retained) initialSeed).2 ∧
      (eagerFinal recursiveDepth (advance initialSeed (count * (bound + 1)))
          (initialMass + count * bound)).1 ⊆
        (tuplePlan (nodePlan limit own height) count bound initialMass
          (fun retained current => eagerFinal recursiveDepth current retained) initialSeed).1 := by
  obtain ⟨consumed, seedAt, paid, retainedMass, lengths, _members⟩ :=
    identity_actual_tuple_prefix_costs graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed
      initialMass bound bounded completedPrefix [] caller before queries seed mass done stopped context
  have prefixCount : completedPrefix.length ≤ count := by
    simp only [List.length_nil, Nat.add_zero] at lengths
    omega
  have queryCount := Nat.mul_le_mul_right (bound + 1) prefixCount
  have paddedMass := Nat.mul_le_mul_right bound prefixCount
  have callbackReserved := tupleReserved_first_callback bits limit own height count bound initialMass
    (fun retained current => eagerFinal recursiveDepth current retained)
    (fun retained current => eagerReserved bits recursiveDepth current retained) initialSeed reserved
  have included := first_callback_le_tuple_of_growth limit own height count bound initialMass
    (fun retained current => eagerFinal recursiveDepth current retained)
    (fun retained current => eagerFinal_ge recursiveDepth current retained) initialSeed
  exact ⟨consumed, seedAt, Nat.le_trans paid queryCount,
    Nat.le_trans retainedMass (Nat.add_le_add_left paddedMass initialMass), callbackReserved, included.1, included.2⟩

end ActualContextCallbackPlanning
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualEmptyTailCallbackResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- An actual own receipt and completed prefix derive the assembled root child resources. -/
private theorem identity_observed_own_tuple_child_inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Unit) (before : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (own : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (packet : Packet formulas solver inventory original memos metadata before)
    (prepared : SourcePruningEnumerationCachedOwn.prepare original.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), own)])
    (fragments : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (history : TupleInputs formulas solver original metadata own
      (staged.map (fun input => (input.1, input.2.1))) fragments reached saved after) :
    ChildInputs formulas solver original metadata before scs (.node edge.entry.key.symbol fragments) reached saved
      (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after) := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  have complete := SourcePruningEnumerationCachedOwn.complete original.checked.native.machine.heap
    before scs edge roots storage realized paths counts flags
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte] at complete
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [projected] at complete
        have impossible := complete.1.symm.trans prepared
        cases impossible
    | some pair =>
        obtain ⟨tries, _projectedResidual⟩ := pair
        simp only [projected] at complete
        obtain ⟨_action, candidate, _prefix, actual, _raw, ownCore, ownCounter, _rest⟩ := complete
        have same := (List.cons.inj (Option.some.inj (actual.symm.trans prepared))).1
        have endpointSame : candidate = own := congrArg Prod.snd same
        have contentsSame := congrArg Prod.fst same
        have tailSame := congrArg Prod.snd contentsSame
        have stagedSame := congrArg Prod.fst tailSame
        subst candidate
        change edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.core.counter tries),
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
              (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.core.counter tries)) indexed.1)) = staged at stagedSame
        have readback : staged.map (fun input => (input.1, input.2.1)) =
            SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries := by
          simp only [← stagedSame, List.map_map, SourcePruningEnumerationEdgeInputs.children]
          rfl
        have ownProtects (held : Nat) (inside : held < before.core.counter)
            (root : IsRoot before.core.representatives held) (avoids : Avoids before.core.representatives held scs) :
            EnumerationDriver.Protected held before.core own.core ∧
              ∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
                Avoids own.core.representatives held bucket := by
          have frame : EnumerationDriver.Protected held before.core own.core := by
            rw [ownCore]
            exact EnumerationDriver.suspension_protected held tries.length before.core packet.safe inside root
          refine ⟨frame, ?_⟩
          intro incoming bucket member
          obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp member
          cases pairSame
          have inherited := descend_avoids own.core.representatives held indexed.2 scs (frame.avoids scs avoids)
          have fresh := descend_avoids own.core.representatives held indexed.2 (suspendedVars before.core.counter tries)
            (frame.avoids _ (fresh_avoids before.core packet.safe.1 held inside tries))
          intro sc listed
          rcases List.mem_append.mp listed with inheritedMember | freshMember
          · exact inherited sc inheritedMember
          · exact fresh sc freshMember
        rw [readback] at history
        exact own_tuple_child_inputs formulas solver original metadata before own edge scs tries residual
          ownCore ownCounter ownProtects fragments reached saved after history
  · simp only [allowed] at complete
    have impossible := Option.some.inj (complete.1.symm.trans prepared)
    cases impossible

end ActualEmptyTailCallbackResources
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualClosedTupleCallback
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance advance_add)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual empty remaining tail derives its real smaller-depth callback resources. -/
private theorem identity_actual_empty_tail_callback_resources
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (limit own height count bound : Nat)
    (workerIH : IdentityEagerEmittedCompleteAtDepth (bits := bits) graph checkEmpty edgesOf formulas solver recursiveDepth)
    (initialInventory : Inventory) (initialMemos : Memos) (handle : Nat)
    (initialQuery : initialMemos.query = capturedQueries)
    (initialPacket : Packet formulas solver initialInventory capturedCaller initialMemos metadata capturedBefore)
    (ready : EnumerationDriver.Ready uv capturedBefore.core)
    (stored : capturedBefore.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv capturedBefore.core)
    (initialFits : Fits initialSeed.2 capturedCaller.checked)
    (initialKnown : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ initialSeed.1)
      capturedCaller.checked.native.machine.heap)
    (initialMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound capturedOwn.core ≤ initialMass)
    (counted : staged.length ≤ count)
    (selectorMembers : ∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows)
    (selectorLengths : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (genuine : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      Available capturedCaller.checked.native.machine.heap child ∧ child.free = [] ∧
      MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
      (∀ sc ∈ bucket, sc.var < capturedOwn.core.counter) ∧ InputsPending capturedOwn.core bucket)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      count bound initialMass (fun retained current => eagerFinal recursiveDepth current retained)
      (fun retained current => eagerReserved bits recursiveDepth current retained) initialSeed)
    (completedPrefix : List Fragment)
    (caller : Caller (bits + 2)) (current : Cached) (queries : Queries)
    (seed : Seed) (mass : Nat) (done : Done) (stopped : Stopped)
    (context : IdentityActualTupleContext graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      completedPrefix [] caller current queries seed mass done stopped) :
    IdentityEmittedCompleteResources formulas solver capturedCaller
      (tuplePlan (nodePlan limit own height) count bound initialMass
        (fun retained current => eagerFinal recursiveDepth current retained) initialSeed)
      (finish uv (done [] caller queries current)) := by
  let entry := advance initialSeed (count * (bound + 1))
  let retained := initialMass + count * bound
  let plan := tuplePlan (nodePlan limit own height) count bound initialMass
    (fun kept current => eagerFinal recursiveDepth current kept) initialSeed
  let fragment : Fragment := .node edge.entry.key.symbol completedPrefix
  let childAfter := SelectedEdge.finish residual fragment current
  let visit := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (resumeWithNarrow (Typing := Unit) (width := bits + 2) visit
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveDepth)
    graph [] none (fun _ _ => none) workFuel metadata uv
  obtain ⟨history, currentFits, currentKnown, currentMass, _remaining, _packet⟩ :=
    identity_actual_context_prefix_resources graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      formulas solver limit own height count bound workerIH initialInventory initialMemos handle initialQuery
      initialPacket ready stored incoming initialFits initialKnown initialMassBound counted selectorMembers selectorLengths
      genuine reserved completedPrefix [] caller current queries seed mass done stopped context
  obtain ⟨prepared, doneSource⟩ := identity_actual_tuple_done_source graph checkEmpty edgesOf recursiveDepth workFuel
    metadata uv capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
    completedPrefix [] caller current queries seed mass done stopped context
  have originalBounds : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      bucket.length ≤ bound := fun child bucket member => (genuine child bucket member).2.2.2.1
  obtain ⟨consumed, seedAt, queryCount, massCeiling, callbackReserved, includedNumeric, includedAlphabet⟩ :=
    identity_actual_empty_tail_callback_plan graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      limit own height count bound originalBounds counted reserved completedPrefix caller current queries seed mass done stopped context
  have entryFits : Fits entry.2 caller.checked := currentFits.mono (by
    rw [seedAt]
    exact SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono initialSeed queryCount)
  have alphabet : seed.1 ⊆ entry.1 := by
    rw [seedAt]
    obtain ⟨extra, counts⟩ := Nat.exists_eq_add_of_le queryCount
    change (advance initialSeed consumed).1 ⊆ (advance initialSeed (count * (bound + 1))).1
    rw [counts, advance_add]
    exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge (advance initialSeed consumed) extra
  have entryKnown : Heap (fun guard => guard ∈ entry.1) caller.checked.native.machine.heap :=
    fun key held found => alphabet (currentKnown key held found)
  have data := identity_observed_own_tuple_child_inputs formulas solver initialInventory capturedCaller initialMemos
    metadata capturedBefore scs edge residual capturedOwn staged initialPacket prepared completedPrefix caller queries current history
  have childMass : SourcePruningEnumerationPrefixAdmission.suspendedBound childAfter.core ≤ retained := by
    change SourcePruningEnumerationPrefixAdmission.suspendedBound current.core ≤ retained
    exact Nat.le_trans currentMass massCeiling
  have doneAt : done [] caller queries current = SourcePruningEnumerationSharedReceiptContinuation.run
      hook capturedCaller capturedQueries
      (some (match SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap workFuel uv fragment childAfter with
        | some finished => .complete fragment caller queries finished
        | none => .finalizeStopped fragment caller queries childAfter)) := by
    simpa only [List.append_nil, hook, visit, fragment, childAfter] using doneSource [] caller queries current
  change IdentityEmittedCompleteResources formulas solver capturedCaller plan (finish uv (done [] caller queries current))
  rw [doneAt]
  cases observedFinish : SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap workFuel uv fragment childAfter with
  | none =>
      constructor
      · intro output member
        cases member
      · trivial
  | some finished =>
      obtain ⟨next, final, finalFuel, canonicalAfter, post, querySame, finalAt,
          finishedPacket, _fragmentBound, _core, finalMass, _stored, _root⟩ :=
        finalize_child_inputs_packet formulas solver capturedCaller caller metadata capturedBefore childAfter uv handle scs
          fragment queries ready stored incoming data
      have observedLater := SourcePruningEnumerationFinalize.run_some_moreFuel
        caller.checked.native.machine.heap workFuel finalFuel uv fragment childAfter finished observedFinish
      have canonicalLater := finalAt workFuel
      rw [Nat.add_comm workFuel finalFuel] at observedLater
      have sameCache : canonicalAfter = finished := Option.some.inj (canonicalLater.symm.trans observedLater)
      subst canonicalAfter
      have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
        Nat.le_trans finalMass childMass
      have callback := identity_callback_emitted_complete_at_any_budget graph checkEmpty edgesOf formulas solver recursiveDepth
        workerIH next caller final finished metadata uv fragment entry retained finishedPacket entryFits entryKnown
        selectorMembers selectorLengths actualMass callbackReserved workFuel
      rw [querySame] at callback
      have enlarged := identity_emitted_complete_mono includedNumeric includedAlphabet callback
      have framed := identity_emitted_complete_post post enlarged
      have actualHook : IdentityEmittedCompleteResources formulas solver capturedCaller plan
          (hook fragment caller queries finished) := by
        simpa only [hook, visit] using framed
      cases observedHook : hook fragment caller queries finished with
      | complete outputs reached saved =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish] using actualHook
      | stopped outputs reason endpoint =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish,
            IdentityEmittedCompleteResources, emitted] using actualHook

/-- The original pointwise target holds for the three actual source context cases. -/
private theorem identity_actual_tuple_at_of_worker
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (capturedCaller : Caller (bits + 2))
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (capturedOwn : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (initialSeed : Seed) (initialMass : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (limit own height count bound : Nat) :
    IdentityActualTupleAt graph checkEmpty edgesOf recursiveDepth workFuel metadata uv capturedCaller capturedQueries
      capturedBefore scs edge residual capturedOwn staged initialSeed initialMass formulas solver limit own height count bound := by
  intro workerIH initialInventory initialMemos handle initialQuery initialPacket ready stored incoming initialFits initialKnown
    initialMassBound counted selectorMembers selectorLengths genuine reserved
  intro completedPrefix inputs caller current queries seed mass done stopped context
  have prefixResources := identity_actual_context_prefix_resources graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
    capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
    formulas solver limit own height count bound workerIH initialInventory initialMemos handle initialQuery
    initialPacket ready stored incoming initialFits initialKnown initialMassBound counted selectorMembers selectorLengths
    genuine reserved completedPrefix inputs caller current queries seed mass done stopped context
  constructor
  · exact ⟨prefixResources.1, prefixResources.2.1, prefixResources.2.2.1, prefixResources.2.2.2.1⟩
  · intro empty
    subst inputs
    exact identity_actual_empty_tail_callback_resources graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      capturedCaller capturedQueries capturedBefore scs edge residual capturedOwn staged initialSeed initialMass
      formulas solver limit own height count bound workerIH initialInventory initialMemos handle initialQuery
      initialPacket ready stored incoming initialFits initialKnown initialMassBound counted selectorMembers selectorLengths
      genuine reserved completedPrefix caller current queries seed mass done stopped context

end ActualClosedTupleCallback
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualGeneralOrdinaryRowPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
open SourcePruningEnumerationSharedSelectedContinuations
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (iterate)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
local notation "Visitor" => List Suspended → Node → Caller (bits + 2) → Cached → Queries →
  (Fragment → Caller (bits + 2) → Queries → Cached → Fold) →
  (ChildDispatch.Observation (bits + 2) → Option Cached → Fold) → Fold
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- An actual row entry derives its nested tuple reservation and current child inputs. -/
private theorem identity_ordinary_row_prefix_reservation
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Unit) (before : Cached)
    (captured : InternedConstructorTemplates.State Symbol Constraint)
    (limit own height bound ceiling : Nat) (initialSeed rowSeed : Seed)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (attempted remaining : List (EdgeValue Symbol Constraint))
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits rowSeed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ rowSeed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (available : Available captured (.node parentEntry rows depth free))
    (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (pending : InputsPending before.core scs)
    (sourceRows : edgesOf (.node parentEntry rows depth free) = attempted ++ edge :: remaining)
    (selectionMembers : ∀ selected ∈ edgesOf (.node parentEntry rows depth free), selected ∈ rows)
    (selectionLength : (edgesOf (.node parentEntry rows depth free)).length ≤ rows.length)
    (shapes : rows.length ≤ limit ∧ ∀ selected ∈ rows, selected.children.length ≤ limit ∧
      ∀ projected residual, SourcePruningEnumerationConstraint.project selected.entry.key.constraint =
        some (projected, residual) → projected.length ≤ own)
    (allowed : arityAllows edge.children.length scs = true)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (scheduled : rowSeed = iterate
      (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current)
      (fallbackPlan bound ceiling continuation initialSeed) attempted.length)
    (reserved : nodeReserved bits limit own (height + 1) bound ceiling continuation admitted initialSeed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1) :
    let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
    let staged := inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1))
    ∃ rowOwn : Cached,
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol, staged, residual), rowOwn)] ∧
      Packet formulas solver inventory caller memos metadata rowOwn ∧
      TupleInputs formulas solver caller metadata rowOwn
        (staged.map (fun input => (input.1, input.2.1))) [] caller memos.query rowOwn ∧
      Fits rowSeed.2 caller.checked ∧
      Heap (fun guard => guard ∈ rowSeed.1) caller.checked.native.machine.heap ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound rowOwn.core ≤ ceiling ∧
      inputs.length ≤ limit ∧
      (∀ child bucket, (child, bucket) ∈ inputs →
        Available captured child ∧ child.free = [] ∧
        MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free) ∧
        MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound + own ∧
        (∀ sc ∈ bucket, sc.var < rowOwn.core.counter) ∧ InputsPending rowOwn.core bucket) ∧
      tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
        limit (bound + own) ceiling continuation admitted rowSeed ∧
      (Le (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation rowSeed).2
          (nodePlan limit own (height + 1) bound ceiling continuation initialSeed).2 ∧
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation rowSeed).1 ⊆
          (nodePlan limit own (height + 1) bound ceiling continuation initialSeed).1) ∧
      ∀ (visit : Visitor) (consume : SelectedEdge.Result (bits + 2) → Fold),
        SourcePruningEnumerationSharedChildVisitors.visitSelected visit consume scs edge caller before memos.query =
          SourcePruningEnumerationSharedChildVisitors.visitChildren visit
            (fun fragments reached saved after =>
              let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
              consume (.complete fragment reached saved (SelectedEdge.finish residual fragment after)))
            (fun completed observation candidate => consume (.stopped completed observation candidate))
            inputs caller rowOwn memos.query := by
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  let staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) := inputs.map (fun input =>
    (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1))
  have selected : edge ∈ rows := by
    apply selectionMembers edge
    rw [sourceRows]
    exact List.mem_append_right attempted List.mem_cons_self
  have indexLt : attempted.length < limit := by
    have selectedLength := selectionLength
    rw [sourceRows, List.length_append, List.length_cons] at selectedLength
    have rowBound := shapes.1
    omega
  have rowReserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted rowSeed := by
    rw [scheduled]
    exact reserved.2 attempted.length indexLt
  have rowForecast :
      Le (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation rowSeed).2
          (nodePlan limit own (height + 1) bound ceiling continuation initialSeed).2 ∧
      (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation rowSeed).1 ⊆
          (nodePlan limit own (height + 1) bound ceiling continuation initialSeed).1 := by
    let first := fallbackPlan bound ceiling continuation initialSeed
    let row := fun current => tuplePlan (nodePlan limit own height)
      limit (bound + own) ceiling continuation current
    have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
      intro current
      exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
        limit (bound + own) ceiling continuation growth current
    have nextSlot : iterate row first (attempted.length + 1) = row rowSeed := by
      rw [SourcePruningEnumerationFiniteReservation.iterate_add]
      rw [scheduled]
      rfl
    have later := iterate_index_le row rowGrowth first (attempted.length + 1) limit (by omega)
    rw [nextSlot] at later
    exact later
  obtain ⟨_roots, _action, rowOwn, _paths, ownReceipt, rowPacket, rowMass, lower, reducing⟩ :=
    ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
      edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
  have actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), rowOwn)] := ownReceipt.2.1
  have emptyPrefix := (identity_captured_actual_prefix_entry formulas solver inventory caller memos metadata
    before scs edge residual rowOwn staged packet actual).2
  obtain ⟨_prepared, _middleRun, _raw, _middleCore, _middleCounter, _middleForest, _middleSafe,
    _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, _middleProtects⟩ := ownReceipt
  have edgeBounds := shapes.2 edge selected
  have triesBound := edgeBounds.2 tries residual projected
  have inputLength : inputs.length ≤ limit := by
    simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx]
      using edgeBounds.1
  have inputFacts : ∀ child bucket, (child, bucket) ∈ inputs →
      Available captured child ∧ child.free = [] ∧
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free) ∧
        MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound + own ∧
      (∀ sc ∈ bucket, sc.var < rowOwn.core.counter) ∧ InputsPending rowOwn.core bucket := by
    intro child bucket member
    obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine child bucket member
    have childRank := lower child bucket member
    obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
    cases same
    have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
    have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
      (suspendedVars before.core.counter tries)
    rw [SourcePruningEnumerationCostBounds.suspended_length] at added
    refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
      ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, childRank, by omega, ?_,
      childBounded, childPending⟩
    simp only [List.length_append]
    omega
  have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound rowOwn.core ≤ ceiling := by
    rw [rowMass]
    exact mass
  exact ⟨rowOwn, actual, rowPacket, emptyPrefix, fits, known, ownMass, inputLength,
    inputFacts, rowReserved, rowForecast, reducing⟩

end ActualGeneralOrdinaryRowPrefix
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualNestedOwnPrefixPreservation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- An actual singleton own receipt identifies its source suspension state. -/
private theorem identity_observed_own_suspension
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Unit) (before : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (own : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (packet : Packet formulas solver inventory caller memos metadata before)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), own)]) :
    ∃ tries : List EqualityTrie.Trie,
      own.core = suspendedState tries.length before.core ∧
      own.core.counter = before.core.counter + tries.length := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  have complete := SourcePruningEnumerationCachedOwn.complete caller.checked.native.machine.heap
    before scs edge roots storage realized paths counts flags
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte] at complete
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [projected] at complete
        have impossible := complete.1.symm.trans prepared
        cases impossible
    | some pair =>
        obtain ⟨tries, projectedResidual⟩ := pair
        simp only [projected] at complete
        obtain ⟨_action, candidate, _prefix, actual, _raw, ownCore, ownCounter, _aligned,
          _forest, _ownPaths, _ownStorage, _ownRealized, _ownCounts, _waiting, _expandable, _ownFlags⟩ := complete
        have endpointSame : candidate = own :=
          congrArg Prod.snd (List.cons.inj (Option.some.inj (actual.symm.trans prepared))).1
        subst candidate
        exact ⟨tries, ownCore, ownCounter⟩
  · simp only [allowed] at complete
    have impossible := Option.some.inj (complete.1.symm.trans prepared)
    cases impossible

/-- The actual nested own receipt retains the outer prefix and starts its full inner prefix. -/
private theorem tuple_inputs_after_observed_own
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (before : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller : Caller (bits + 2)) (queries : SourceEndpointMemo.Memos) (current : Cached)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (residual : Option Constraint) (own : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (previous : TupleInputs formulas solver original metadata before inputs completed caller queries current)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge current =
      some [((edge.entry.key.symbol, staged, residual), own)]) :
    TupleInputs formulas solver original metadata before inputs completed caller queries own ∧
      TupleInputs formulas solver caller metadata own
        (staged.map (fun input => (input.1, input.2.1))) [] caller queries own := by
  obtain ⟨inventory, memos, post, query, packet, previousGrowth, previousOrigin,
    previousProtected, previousRootsProtected, previousReferences, previousBounds, previousHistory⟩ := previous
  have actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge current =
      some [((edge.entry.key.symbol, staged, residual), own)] := prepared
  obtain ⟨ownPacket, nestedPrefix⟩ := identity_captured_actual_prefix_entry
    formulas solver inventory caller memos metadata current scs edge residual own staged packet actual
  obtain ⟨tries, ownCore, ownCounter⟩ := identity_observed_own_suspension
    formulas solver inventory caller memos metadata current scs edge residual own staged packet actual
  have growth : current.core.counter ≤ own.core.counter := by
    rw [ownCounter]
    omega
  have origin : EnumeratedOrigin current.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length current.core
  have protects (held : Nat) (inside : held < current.core.counter)
      (root : IsRoot current.core.representatives held) :
      EnumerationDriver.Protected held current.core own.core := by
    rw [ownCore]
    exact EnumerationDriver.suspension_protected held tries.length current.core packet.safe inside root
  have protectsEnumerated (held : Nat) (fragment : Fragment)
      (stored : current.core.values[held]? = some (.enumerated fragment)) :
      EnumerationDriver.Protected held current.core own.core := by
    obtain ⟨inside, root⟩ := enumerated_root current.core packet.safe held fragment stored
    exact protects held inside root
  have protectsOriginalRoot (held : Nat) (inside : held < before.core.counter)
      (root : IsRoot before.core.representatives held)
      (avoids : ∀ child bucket, (child, bucket) ∈ inputs → Avoids before.core.representatives held bucket) :
      EnumerationDriver.Protected held current.core own.core := by
    have first := previousRootsProtected held inside root avoids
    exact protects held (Nat.lt_of_lt_of_le inside previousGrowth) first.root
  constructor
  · refine ⟨inventory, memos, post, query, ownPacket, Nat.le_trans previousGrowth growth,
      previousOrigin.trans origin, ?_, ?_, ?_, ?_, ?_⟩
    · intro held fragment stored
      have first := previousProtected held fragment stored
      exact first.trans (protectsEnumerated held fragment (first.value.trans stored))
    · intro held inside root avoids
      exact (previousRootsProtected held inside root avoids).trans
        (protectsOriginalRoot held inside root avoids)
    · intro allowed valid supplied future
      rw [ownCore]
      exact EnumerationReferences.suspension_allowed allowed tries.length current.core
        (previousReferences allowed valid supplied future)
    · intro fragment member
      exact fragmentBound_mono _ _ growth fragment (previousBounds fragment member)
    · intro fragment member
      obtain ⟨fragmentPending, fragmentSeparate⟩ := previousHistory fragment member
      refine ⟨pendingFragment_preserved current.core own.core packet.safe ownPacket.safe
        growth fragment (previousBounds fragment member) fragmentPending origin protectsEnumerated, ?_⟩
      intro held inside root avoids
      have lastProtection := protectsOriginalRoot held inside root avoids
      exact (fragmentAvoid_classes current.core.representatives own.core.representatives
        held fragment lastProtection.classes).mpr (fragmentSeparate held inside root avoids)
  · rw [query] at nestedPrefix
    exact nestedPrefix

end ActualNestedOwnPrefixPreservation
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualNestedChildTwoPrefixes
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual own receipt identifies every source input bucket and its suspension. -/
private theorem identity_observed_own_input_provenance
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Unit) (before : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (own : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (packet : Packet formulas solver inventory caller memos metadata before)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), own)]) :
    ∃ tries : List EqualityTrie.Trie,
      own.core = suspendedState tries.length before.core ∧
      staged.map (fun input => (input.1, input.2.1)) =
        SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  have complete := SourcePruningEnumerationCachedOwn.complete caller.checked.native.machine.heap
    before scs edge roots storage realized paths counts flags
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte] at complete
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [projected] at complete
        have impossible := complete.1.symm.trans prepared
        cases impossible
    | some pair =>
        obtain ⟨tries, projectedResidual⟩ := pair
        simp only [projected] at complete
        obtain ⟨_action, candidate, _prefix, actual, _raw, ownCore, _ownCounter, _aligned,
          _forest, _ownPaths, _ownStorage, _ownRealized, _ownCounts, _waiting, _expandable, _ownFlags⟩ := complete
        have pairSame := (List.cons.inj (Option.some.inj (actual.symm.trans prepared))).1
        have endpointSame : candidate = own := congrArg Prod.snd pairSame
        have contentsSame := congrArg Prod.fst pairSame
        have stagedSame := congrArg Prod.fst (congrArg Prod.snd contentsSame)
        subst candidate
        change edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.core.counter tries),
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
              (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.core.counter tries)) indexed.1)) = staged at stagedSame
        refine ⟨tries, ownCore, ?_⟩
        simp only [← stagedSame, List.map_map, SourcePruningEnumerationEdgeInputs.children]
        rfl
  · simp only [allowed] at complete
    have impossible := Option.some.inj (complete.1.symm.trans prepared)
    cases impossible

/-- An actual inner child preserves the outer prefix and extends the inner prefix. -/
private theorem tuple_inputs_after_nested_child
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (before : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller : Caller (bits + 2)) (queries : SourceEndpointMemo.Memos) (current : Cached)
    (parent : Node) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (residual : Option Constraint) (own : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (incoming : Node) (bucket : List Suspended) (fragment : Fragment)
    (reached : Caller (bits + 2)) (saved : SourceEndpointMemo.Memos) (after : Cached)
    (previous : TupleInputs formulas solver original metadata before inputs completed caller queries current)
    (sourceHead : (parent, scs) ∈ inputs)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge current =
      some [((edge.entry.key.symbol, staged, residual), own)])
    (member : (incoming, bucket) ∈ staged.map (fun input => (input.1, input.2.1)))
    (pending : InputsPending own.core bucket)
    (head : ChildInputs formulas solver caller metadata own bucket fragment reached saved after) :
    TupleInputs formulas solver original metadata before inputs completed reached saved after ∧
      TupleInputs formulas solver caller metadata own
        (staged.map (fun input => (input.1, input.2.1))) [fragment] reached saved after := by
  obtain ⟨outerOwn, innerOwn⟩ := tuple_inputs_after_observed_own formulas solver original metadata before
    inputs completed caller queries current scs edge residual own staged previous prepared
  have innerAfter := tuple_inputs_extend_current_head formulas solver caller metadata own
    (staged.map (fun input => (input.1, input.2.1))) [] caller queries own
    incoming bucket fragment reached saved after innerOwn member pending head
  obtain ⟨currentInventory, currentMemos, _beforePost, _beforeQuery, currentPacket,
    beforeGrowth, _beforeOrigin, _beforeProtected, beforeRootsProtected, _beforeReferences,
    _beforeBounds, _beforeHistory⟩ := previous
  obtain ⟨tries, ownCore, readback⟩ := identity_observed_own_input_provenance formulas solver
    currentInventory caller currentMemos metadata current scs edge residual own staged currentPacket prepared
  have canonicalMember : (incoming, bucket) ∈
      SourcePruningEnumerationEdgeInputs.children edge scs current.core.counter tries := by
    rw [← readback]
    exact member
  have ownFrame (held : Nat) (inside : held < current.core.counter)
      (root : IsRoot current.core.representatives held) :
      EnumerationDriver.Protected held current.core own.core := by
    rw [ownCore]
    exact EnumerationDriver.suspension_protected held tries.length current.core currentPacket.safe inside root
  have childAvoids (held : Nat) (inside : held < current.core.counter)
      (root : IsRoot current.core.representatives held)
      (avoids : Avoids current.core.representatives held scs) :
      Avoids own.core.representatives held bucket := by
    have frame := ownFrame held inside root
    obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp canonicalMember
    cases pairSame
    have inherited := descend_avoids own.core.representatives held indexed.2 scs (frame.avoids scs avoids)
    have fresh := descend_avoids own.core.representatives held indexed.2
      (suspendedVars current.core.counter tries)
      (frame.avoids _ (fresh_avoids current.core currentPacket.safe.1 held inside tries))
    intro sc listed
    rcases List.mem_append.mp listed with inheritedMember | freshMember
    · exact inherited sc inheritedMember
    · exact fresh sc freshMember
  have childAllowed (allowed : Nat → Prop)
      (inherited : EnumerationReferences.InputsAllowed allowed scs)
      (future : ∀ uv, current.core.counter ≤ uv → allowed uv) :
      EnumerationReferences.InputsAllowed allowed bucket := by
    have fresh := EnumerationReferences.suspended_allowed allowed current.core.counter
      current.core.counter tries (Nat.le_refl _) future
    obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp canonicalMember
    cases pairSame
    have oldAllowed := EnumerationReferences.descend_allowed allowed scs indexed.2 inherited
    have newAllowed := EnumerationReferences.descend_allowed allowed
      (suspendedVars current.core.counter tries) indexed.2 fresh
    intro sc listed
    rcases List.mem_append.mp listed with inheritedMember | freshMember
    · exact oldAllowed sc inheritedMember
    · exact newAllowed sc freshMember
  obtain ⟨_ownInventory, _ownMemos, previousPost, _previousQuery, ownPacket, previousGrowth,
    previousOrigin, previousProtected, previousRootsProtected, previousReferences,
    previousBounds, previousHistory⟩ := outerOwn
  obtain ⟨next, final, headPost, query, afterPacket, growth, origin, protects,
    references, _fragmentBound, _fragmentPending, _fragmentSeparate⟩ := head
  have protectsEnumerated (held : Nat) (old : Fragment)
      (stored : own.core.values[held]? = some (.enumerated old)) :
      EnumerationDriver.Protected held own.core after.core := by
    obtain ⟨inside, root⟩ := enumerated_root own.core ownPacket.safe held old stored
    exact protects held inside root (pending held old stored)
  have protectsOriginalRoot (held : Nat) (inside : held < before.core.counter)
      (root : IsRoot before.core.representatives held)
      (avoids : ∀ child retained, (child, retained) ∈ inputs →
        Avoids before.core.representatives held retained) :
      EnumerationDriver.Protected held own.core after.core := by
    have atOwn := previousRootsProtected held inside root avoids
    have atCurrent := beforeRootsProtected held inside root avoids
    have atBucket := childAvoids held (Nat.lt_of_lt_of_le inside beforeGrowth) atCurrent.root
      (atCurrent.avoids scs (avoids parent scs sourceHead))
    exact protects held (Nat.lt_of_lt_of_le inside previousGrowth) atOwn.root atBucket
  constructor
  · refine ⟨next, final, previousPost.trans headPost, query, afterPacket,
      Nat.le_trans previousGrowth growth, previousOrigin.trans origin, ?_, ?_, ?_, ?_, ?_⟩
    · intro held old stored
      have first := previousProtected held old stored
      exact first.trans (protectsEnumerated held old (first.value.trans stored))
    · intro held inside root avoids
      exact (previousRootsProtected held inside root avoids).trans
        (protectsOriginalRoot held inside root avoids)
    · intro allowed valid supplied future
      apply references allowed (previousReferences allowed valid supplied future)
      · exact childAllowed allowed (supplied parent scs sourceHead)
          (fun uv lower => future uv (Nat.le_trans beforeGrowth lower))
      · intro uv lower
        exact future uv (Nat.le_trans previousGrowth lower)
    · intro child included
      exact fragmentBound_mono _ _ growth child (previousBounds child included)
    · intro child included
      obtain ⟨childPending, childSeparate⟩ := previousHistory child included
      refine ⟨pendingFragment_preserved own.core after.core ownPacket.safe afterPacket.safe
        growth child (previousBounds child included) childPending origin protectsEnumerated, ?_⟩
      intro held inside root avoids
      have lastProtection := protectsOriginalRoot held inside root avoids
      exact (fragmentAvoid_classes own.core.representatives after.core.representatives
        held child lastProtection.classes).mpr (childSeparate held inside root avoids)
  · exact innerAfter

end ActualNestedChildTwoPrefixes
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualNestedPrefixForwardComposition
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A current inner prefix retains the outer prefix at its actual reached endpoint. -/
private theorem tuple_inputs_after_nested_prefix
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (before : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller : Caller (bits + 2)) (queries : SourceEndpointMemo.Memos) (current : Cached)
    (parent : Node) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (residual : Option Constraint) (own : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (innerCompleted : List Fragment)
    (reached : Caller (bits + 2)) (saved : SourceEndpointMemo.Memos) (after : Cached)
    (previous : TupleInputs formulas solver original metadata before inputs completed caller queries current)
    (sourceHead : (parent, scs) ∈ inputs)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge current =
      some [((edge.entry.key.symbol, staged, residual), own)])
    (inner : TupleInputs formulas solver caller metadata own
      (staged.map (fun input => (input.1, input.2.1))) innerCompleted reached saved after) :
    TupleInputs formulas solver original metadata before inputs completed reached saved after := by
  have atOwn := (tuple_inputs_after_observed_own formulas solver original metadata before
    inputs completed caller queries current scs edge residual own staged previous prepared).1
  obtain ⟨currentInventory, currentMemos, _beforePost, _beforeQuery, currentPacket,
    beforeGrowth, _beforeOrigin, _beforeProtected, beforeRootsProtected, _beforeReferences,
    _beforeBounds, _beforeHistory⟩ := previous
  obtain ⟨tries, ownCore, readback⟩ := identity_observed_own_input_provenance formulas solver
    currentInventory caller currentMemos metadata current scs edge residual own staged currentPacket prepared
  have ownFrame (held : Nat) (inside : held < current.core.counter)
      (root : IsRoot current.core.representatives held) :
      EnumerationDriver.Protected held current.core own.core := by
    rw [ownCore]
    exact EnumerationDriver.suspension_protected held tries.length current.core currentPacket.safe inside root
  have innerAvoids (held : Nat) (inside : held < current.core.counter)
      (root : IsRoot current.core.representatives held)
      (avoids : Avoids current.core.representatives held scs) :
      ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
        Avoids own.core.representatives held bucket := by
    intro child bucket member
    rw [readback] at member
    have frame := ownFrame held inside root
    obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp member
    cases pairSame
    have inherited := descend_avoids own.core.representatives held indexed.2 scs (frame.avoids scs avoids)
    have fresh := descend_avoids own.core.representatives held indexed.2
      (suspendedVars current.core.counter tries)
      (frame.avoids _ (fresh_avoids current.core currentPacket.safe.1 held inside tries))
    intro sc listed
    rcases List.mem_append.mp listed with inheritedMember | freshMember
    · exact inherited sc inheritedMember
    · exact fresh sc freshMember
  have innerAllowed (allowed : Nat → Prop)
      (inherited : EnumerationReferences.InputsAllowed allowed scs)
      (future : ∀ uv, current.core.counter ≤ uv → allowed uv) :
      ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
        EnumerationReferences.InputsAllowed allowed bucket := by
    intro child bucket member
    rw [readback] at member
    have fresh := EnumerationReferences.suspended_allowed allowed current.core.counter
      current.core.counter tries (Nat.le_refl _) future
    obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp member
    cases pairSame
    have oldAllowed := EnumerationReferences.descend_allowed allowed scs indexed.2 inherited
    have newAllowed := EnumerationReferences.descend_allowed allowed
      (suspendedVars current.core.counter tries) indexed.2 fresh
    intro sc listed
    rcases List.mem_append.mp listed with inheritedMember | freshMember
    · exact oldAllowed sc inheritedMember
    · exact newAllowed sc freshMember
  obtain ⟨_ownInventory, _ownMemos, previousPost, _previousQuery, ownPacket, previousGrowth,
    previousOrigin, previousProtected, previousRootsProtected, previousReferences,
    previousBounds, previousHistory⟩ := atOwn
  obtain ⟨next, final, innerPost, query, afterPacket, growth, origin, protectsEnumerated,
    protectsRoots, references, _innerBounds, _innerHistory⟩ := inner
  have protectsOriginalRoot (held : Nat) (inside : held < before.core.counter)
      (root : IsRoot before.core.representatives held)
      (avoids : ∀ child bucket, (child, bucket) ∈ inputs →
        Avoids before.core.representatives held bucket) :
      EnumerationDriver.Protected held own.core after.core := by
    have atOwnRoot := previousRootsProtected held inside root avoids
    have atCurrent := beforeRootsProtected held inside root avoids
    exact protectsRoots held (Nat.lt_of_lt_of_le inside previousGrowth) atOwnRoot.root
      (innerAvoids held (Nat.lt_of_lt_of_le inside beforeGrowth) atCurrent.root
        (atCurrent.avoids scs (avoids parent scs sourceHead)))
  refine ⟨next, final, previousPost.trans innerPost, query, afterPacket,
    Nat.le_trans previousGrowth growth, previousOrigin.trans origin, ?_, ?_, ?_, ?_, ?_⟩
  · intro held fragment stored
    have first := previousProtected held fragment stored
    exact first.trans (protectsEnumerated held fragment (first.value.trans stored))
  · intro held inside root avoids
    exact (previousRootsProtected held inside root avoids).trans
      (protectsOriginalRoot held inside root avoids)
  · intro allowed valid supplied future
    apply references allowed (previousReferences allowed valid supplied future)
    · exact innerAllowed allowed (supplied parent scs sourceHead)
        (fun uv lower => future uv (Nat.le_trans beforeGrowth lower))
    · intro uv lower
      exact future uv (Nat.le_trans previousGrowth lower)
  · intro fragment member
    exact fragmentBound_mono _ _ growth fragment (previousBounds fragment member)
  · intro fragment member
    obtain ⟨fragmentPending, fragmentSeparate⟩ := previousHistory fragment member
    refine ⟨pendingFragment_preserved own.core after.core ownPacket.safe afterPacket.safe
      growth fragment (previousBounds fragment member) fragmentPending origin protectsEnumerated, ?_⟩
    intro held inside root avoids
    have lastProtection := protectsOriginalRoot held inside root avoids
    exact (fragmentAvoid_classes own.core.representatives after.core.representatives
      held fragment lastProtection.classes).mpr (fragmentSeparate held inside root avoids)

end ActualNestedPrefixForwardComposition
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationFiniteReservation (iterate iterate_add)
private inductive IdentityReservationGoal where
  | worker (depth : Nat) (seed : Seed) (ceiling : Nat)
  | node (limit own height bound ceiling : Nat)
      (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
  | rows (limit own height count bound ceiling : Nat)
      (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
  | tuple (limit own height count bound ceiling : Nat)
      (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
  | fallback (bound ceiling : Nat)
      (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
  | callback (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
      (seed : Seed) (ceiling : Nat)

private noncomputable def IdentityReservationGoal.forecast : IdentityReservationGoal → Seed
  | .worker depth seed ceiling => eagerFinal depth seed ceiling
  | .node limit own height bound ceiling continuation _admitted seed =>
      nodePlan limit own height bound ceiling continuation seed
  | .rows limit own height count bound ceiling continuation _admitted seed =>
      iterate (fun current => tuplePlan (nodePlan limit own height)
        limit (bound + own) ceiling continuation current) seed count
  | .tuple limit own height count bound ceiling continuation _admitted seed =>
      tuplePlan (nodePlan limit own height) count bound ceiling continuation seed
  | .fallback bound ceiling continuation _admitted seed => fallbackPlan bound ceiling continuation seed
  | .callback continuation _admitted seed ceiling => continuation ceiling seed

private noncomputable def IdentityReservationGoal.reserved (bits : Nat) : IdentityReservationGoal → Prop
  | .worker depth seed ceiling => eagerReserved bits depth seed ceiling
  | .node limit own height bound ceiling continuation admitted seed =>
      nodeReserved bits limit own height bound ceiling continuation admitted seed
  | .rows limit own height count bound ceiling continuation admitted seed =>
      ∀ index, index < count →
        tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
          limit (bound + own) ceiling continuation admitted
          (iterate (fun current => tuplePlan (nodePlan limit own height)
            limit (bound + own) ceiling continuation current) seed index)
  | .tuple limit own height count bound ceiling continuation admitted seed =>
      tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
        count bound ceiling continuation admitted seed
  | .fallback bound ceiling _continuation admitted seed => fallbackReserved bits bound ceiling admitted seed
  | .callback _continuation admitted seed ceiling => admitted ceiling seed

-- Every position has a source in one original reserved worker plan.
-- No rule supplies an arbitrary later seed or an arbitrary later capacity.
private inductive IdentityReservationPosition (bits : Nat) (root : IdentityReservationGoal) :
    IdentityReservationGoal → Prop where
  | root : IdentityReservationPosition bits root root
  | prepared {depth : Nat} {seed : Seed} {ceiling : Nat}
      (origin : IdentityReservationPosition bits root (.worker (depth + 1) seed ceiling)) :
      IdentityReservationPosition bits root
        (.node
          (SourceCurrentConstrainedCapTargetForecast.scalar
            (SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed).2)
          (SourcePruningEnumerationGuardWidth.width
            (SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed).1)
          (SourceCurrentConstrainedCapTargetForecast.scalar
            (SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed).2)
          ceiling ceiling (fun retained current => eagerFinal depth current retained)
          (fun retained current => eagerReserved bits depth current retained)
          (SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed))
  | nodeFallback {limit own height bound ceiling : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root
        (.node limit own height bound ceiling continuation admitted seed)) :
      IdentityReservationPosition bits root (.fallback bound ceiling continuation admitted seed)
  | nodeRows {limit own height bound ceiling : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root
        (.node limit own (height + 1) bound ceiling continuation admitted seed)) :
      IdentityReservationPosition bits root
        (.rows limit own height limit bound ceiling continuation admitted
          (fallbackPlan bound ceiling continuation seed))
  | rowsBoundary {limit own height count bound ceiling index : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root
        (.rows limit own height count bound ceiling continuation admitted seed))
      (within : index ≤ count) :
      IdentityReservationPosition bits root
        (.rows limit own height (count - index) bound ceiling continuation admitted
          (iterate (fun current => tuplePlan (nodePlan limit own height)
            limit (bound + own) ceiling continuation current) seed index))
  | rowHead {limit own height count bound ceiling : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root
        (.rows limit own height (count + 1) bound ceiling continuation admitted seed)) :
      IdentityReservationPosition bits root
        (.tuple limit own height limit (bound + own) ceiling continuation admitted seed)
  | tupleHead {limit own height count bound ceiling : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root
        (.tuple limit own height (count + 1) bound ceiling continuation admitted seed)) :
      IdentityReservationPosition bits root
        (.node limit own height bound ceiling
          (fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current)
          (fun retained current => tupleReserved (nodePlan limit own height)
            (nodeReserved bits limit own height) count bound retained continuation admitted current) seed)
  | tupleFinishPad {limit own height count bound ceiling : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root
        (.tuple limit own height count bound ceiling continuation admitted seed)) :
      IdentityReservationPosition bits root
        (.callback continuation admitted (advance seed (count * (bound + 1))) (ceiling + count * bound))
  | fallbackFinish {bound ceiling : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root (.fallback bound ceiling continuation admitted seed)) :
      IdentityReservationPosition bits root
        (.callback continuation admitted (advance seed (bound + 1)) (ceiling + bound))
  | tupleTail {limit own height count bound ceiling : Nat}
      {continuation : Nat → Seed → Seed} {admitted : Nat → Seed → Prop} {seed : Seed}
      (origin : IdentityReservationPosition bits root
        (.callback
          (fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current)
          (fun retained current => tupleReserved (nodePlan limit own height)
            (nodeReserved bits limit own height) count bound retained continuation admitted current) seed ceiling)) :
      IdentityReservationPosition bits root
        (.tuple limit own height count bound ceiling continuation admitted seed)
  | identityWorker {depth : Nat} {seed : Seed} {ceiling : Nat}
      (origin : IdentityReservationPosition bits root
        (.callback (fun retained current => eagerFinal depth current retained)
          (fun retained current => eagerReserved bits depth current retained) seed ceiling)) :
      IdentityReservationPosition bits root (.worker depth seed ceiling)

-- The source execution obligations remain open.
-- Reachable forecast profiles and alphabets lie within the original forecast.
-- A SOURCE prefix must also derive its actual Packet/Fits/Heap/mass at that position.
-- The path alone supplies no native effect or source execution invariant.

section OrderedPositionAdmission
attribute [local irreducible] nodeReserved

/-- Every ordered position inherits admission from its original reservation. -/
private theorem identity_reservation_position_reserved
    (bits : Nat) (root goal : IdentityReservationGoal)
    (position : IdentityReservationPosition bits root goal)
    (reserved : IdentityReservationGoal.reserved bits root) :
    IdentityReservationGoal.reserved bits goal := by
  induction position with
  | root => exact reserved
  | prepared origin ih =>
      simpa only [IdentityReservationGoal.reserved, eagerReserved] using ih
  | nodeFallback origin ih =>
      exact nodeReserved_fallback bits _ _ _ _ _ _ _ _ ih
  | nodeRows origin ih =>
      simp only [IdentityReservationGoal.reserved, nodeReserved] at ih
      exact ih.2
  | @rowsBoundary limit own height count bound ceiling index continuation admitted seed origin within ih =>
      intro next nextInside
      have originalInside : index + next < count := by omega
      simpa only [iterate_add] using ih (index + next) originalInside
  | rowHead origin ih => exact ih 0 (Nat.zero_lt_succ _)
  | tupleHead origin ih => exact ih
  | tupleFinishPad origin ih =>
      exact tupleReserved_first_callback bits _ _ _ _ _ _ _ _ _ ih
  | fallbackFinish origin ih => exact ih.2
  | tupleTail origin ih => exact ih
  | identityWorker origin ih => exact ih

end OrderedPositionAdmission
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualCallbackFrames
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
local notation "ChildDone" => Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Visitor" => List Suspended → Node → Caller (bits + 2) → Cached → Queries → ChildDone →
  (ChildDispatch.Observation (bits + 2) → Option Cached → Fold) → Fold

/-- Store the literal root callback or one literal selected-row parent tail. -/
private inductive IdentityActualCallbackFrame (bits : Nat) where
  | captured (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
      (caller : Caller (bits + 2)) (queries : Queries)
  | selected (parent : IdentityActualCallbackFrame bits)
      (completedPrefix : List Fragment) (rest : List (Node × List Suspended))
      (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
      (caller : Caller (bits + 2)) (queries : Queries)
      (parentHeight remainingCount parentBound : Nat)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Use the actual remaining-parent-tuple closure after an assembled child. -/
private noncomputable def identity_actual_parent_tail
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint)) (workFuel : Nat)
    (callbacks : Done × Stopped) (completedPrefix : List Fragment)
    (rest : List (Node × List Suspended)) : ChildDone :=
  fun fragment reached saved after =>
    SourcePruningEnumerationSharedChildVisitors.visitChildren
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        workFuel workFuel workFuel workFuel workFuel edgesOf)
      (fun fragments => callbacks.1 (completedPrefix ++ fragment :: fragments))
      (fun completed => callbacks.2 (completedPrefix ++ fragment :: completed))
      rest reached after saved

/-- Evaluate only the actual source closures stored in the callback frame. -/
private noncomputable def identity_actual_frame_callbacks
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) : IdentityActualCallbackFrame bits → Done × Stopped
  | .captured edge residual caller queries =>
      let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (resumeWithNarrow (Typing := Unit) (width := bits + 2)
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
          none (fun _ _ => none) workFuel recursiveDepth)
        graph [] none (fun _ _ => none) workFuel metadata uv
      (fun fragments reached saved after =>
        let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
        let middle := SelectedEdge.finish residual fragment after
        match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel uv fragment middle with
        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
            (some (.complete fragment reached saved finished))
        | none => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
            (some (.finalizeStopped fragment reached saved middle)),
       fun completed observation candidate => SourcePruningEnumerationSharedReceiptContinuation.run
         hook caller queries (some (.stopped completed observation candidate)))
  | .selected parent completedPrefix rest edge residual caller queries _parentHeight _remainingCount _parentBound =>
      let inherited := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv parent
      let tail := identity_actual_parent_tail checkEmpty edgesOf workFuel inherited completedPrefix rest
      (fun fragments reached saved after =>
        let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
        SourcePruningEnumerationSharedEagerChildren.consumeSelected tail caller queries
          (.complete fragment reached saved (SelectedEdge.finish residual fragment after)),
       fun completed observation candidate => SourcePruningEnumerationSharedEagerChildren.consumeSelected
         tail caller queries (.stopped completed observation candidate))

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- Retain the mathematical parent tail inside every selected-row callback. -/
private noncomputable def identity_actual_frame_plan (recursiveDepth limit own : Nat) :
    IdentityActualCallbackFrame bits → Nat → Seed → Seed
  | .captured _edge _residual _caller _queries => fun retained current => eagerFinal recursiveDepth current retained
  | .selected parent _completed _rest _edge _residual _caller _queries parentHeight remainingCount parentBound =>
      fun retained current => tuplePlan (nodePlan limit own parentHeight)
        remainingCount parentBound retained (identity_actual_frame_plan recursiveDepth limit own parent) current

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- Store capacity for the exact mathematical parent tail, without a native resource provider. -/
private noncomputable def identity_actual_frame_reserved (bits recursiveDepth limit own : Nat) :
    IdentityActualCallbackFrame bits → Nat → Seed → Prop
  | .captured _edge _residual _caller _queries => fun retained current => eagerReserved bits recursiveDepth current retained
  | .selected parent _completed _rest _edge _residual _caller _queries parentHeight remainingCount parentBound =>
      fun retained current => tupleReserved (nodePlan limit own parentHeight) (nodeReserved bits limit own parentHeight)
        remainingCount parentBound retained (identity_actual_frame_plan recursiveDepth limit own parent)
        (identity_actual_frame_reserved bits recursiveDepth limit own parent) current

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- Every actual callback frame retains its forecast input profile and alphabet. -/
private theorem identity_actual_frame_plan_ge
    (recursiveDepth limit own : Nat) (frame : IdentityActualCallbackFrame bits) :
    ∀ retained current,
      Le current.2 (identity_actual_frame_plan recursiveDepth limit own frame retained current).2 ∧
      current.1 ⊆ (identity_actual_frame_plan recursiveDepth limit own frame retained current).1 := by
  induction frame with
  | captured _edge _residual _caller _queries =>
      intro retained current
      exact eagerFinal_ge recursiveDepth current retained
  | selected parent _completedPrefix _rest _edge _residual _caller _queries parentHeight remainingCount parentBound ih =>
      intro retained current
      exact tuplePlan_ge (nodePlan limit own parentHeight) (nodePlan_ge limit own parentHeight)
        remainingCount parentBound retained (identity_actual_frame_plan recursiveDepth limit own parent) ih current

/-- The generated root frame is the literal actual captured-row operation. -/
private theorem identity_captured_frame_generation
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (caller : Caller (bits + 2)) (queries : Queries)
    (before own : Cached) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (residual : Option Constraint)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), own)]) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
      (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
      (resumeWithNarrow (Typing := Unit) (width := bits + 2) child
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) workFuel recursiveDepth)
      graph [] none (fun _ _ => none) workFuel metadata uv
    let callbacks := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.captured edge residual caller queries)
    SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook workFuel uv scs edge caller queries before =
      SourcePruningEnumerationSharedChildVisitors.visitChildren child callbacks.1 callbacks.2
        (staged.map (fun input => (input.1, input.2.1))) caller own queries := by
  dsimp only
  rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
  simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared, identity_actual_frame_callbacks]
  rfl

/-- The actual selected-row callback invokes its literal parent tail and retains its receipt. -/
private theorem identity_selected_frame_callback
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (parent : IdentityActualCallbackFrame bits)
    (completedPrefix : List Fragment) (rest : List (Node × List Suspended))
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
    (caller : Caller (bits + 2)) (queries : Queries) (parentHeight remainingCount parentBound : Nat)
    (fragments : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached) :
    let inherited := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv parent
    let tail := identity_actual_parent_tail checkEmpty edgesOf workFuel inherited completedPrefix rest
    let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
    let returned := SelectedEdge.finish residual fragment after
    (identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.selected parent completedPrefix rest edge residual caller queries parentHeight remainingCount parentBound)).1
      fragments reached saved after =
      match tail fragment reached saved returned with
      | .complete processed outputs finalCaller finalQueries =>
          .complete (.complete fragment reached saved returned :: processed) outputs finalCaller finalQueries
      | .stopped processed outputs current =>
          .stopped (.complete fragment reached saved returned :: processed) outputs current := by
  dsimp only
  simp only [identity_actual_frame_callbacks, SourcePruningEnumerationSharedEagerChildren.consumeSelected]
  cases identity_actual_parent_tail checkEmpty edgesOf workFuel
      (identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv parent)
      completedPrefix rest (.node edge.entry.key.symbol fragments) reached saved
      (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after) <;> rfl

end ActualCallbackFrames
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualCallbackFrameHandoff
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
open SourcePruningEnumerationSharedSelectedContinuations
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual completed inner tuple derives its literal parent-tail entry and reservation. -/
private theorem identity_selected_frame_actual_handoff
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (limit own innerHeight innerCount innerBound innerMass : Nat)
    (innerSeed : Seed) (parent : IdentityActualCallbackFrame bits)
    (parentHeight remainingCount parentBound : Nat)
    (original : Caller (bits + 2)) (scopeBefore : Cached)
    (inputs : List (Node × List Suspended)) (completedPrefix : List Fragment)
    (rest : List (Node × List Suspended))
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached)
    (incoming : Node) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (residual : Option Constraint) (middle : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (fragments : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (previous : TupleInputs formulas solver original metadata scopeBefore inputs completedPrefix caller queries before)
    (member : (incoming, scs) ∈ inputs)
    (pending : InputsPending before.core scs)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, staged, residual), middle)])
    (history : TupleInputs formulas solver caller metadata middle
      (staged.map (fun input => (input.1, input.2.1))) fragments reached saved after)
    (currentFits : Fits innerSeed.2 reached.checked)
    (currentKnown : Heap (fun guard => guard ∈ innerSeed.1) reached.checked.native.machine.heap)
    (currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ innerMass)
    (counted : rest.length ≤ remainingCount)
    (reserved : tupleReserved (nodePlan limit own innerHeight) (nodeReserved bits limit own innerHeight)
      innerCount innerBound innerMass
      (identity_actual_frame_plan recursiveDepth limit own
        (.selected parent completedPrefix rest edge residual caller queries parentHeight remainingCount parentBound))
      (identity_actual_frame_reserved bits recursiveDepth limit own
        (.selected parent completedPrefix rest edge residual caller queries parentHeight remainingCount parentBound)) innerSeed) :
    let frame := IdentityActualCallbackFrame.selected parent completedPrefix rest edge residual caller queries
      parentHeight remainingCount parentBound
    let callbackSeed := advance innerSeed (innerCount * (innerBound + 1))
    let callbackMass := innerMass + innerCount * innerBound
    let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
    let returned := SelectedEdge.finish residual fragment after
    ChildInputs formulas solver caller metadata before scs fragment reached saved returned ∧
    TupleInputs formulas solver original metadata scopeBefore inputs
      (completedPrefix ++ [fragment]) reached saved returned ∧
    Fits callbackSeed.2 reached.checked ∧
    Heap (fun guard => guard ∈ callbackSeed.1) reached.checked.native.machine.heap ∧
    SourcePruningEnumerationPrefixAdmission.suspendedBound returned.core ≤ callbackMass ∧
    rest.length ≤ remainingCount ∧
    tupleReserved (nodePlan limit own parentHeight) (nodeReserved bits limit own parentHeight)
      remainingCount parentBound callbackMass
      (identity_actual_frame_plan recursiveDepth limit own parent)
      (identity_actual_frame_reserved bits recursiveDepth limit own parent) callbackSeed ∧
    (Le (tuplePlan (nodePlan limit own parentHeight) remainingCount parentBound callbackMass
        (identity_actual_frame_plan recursiveDepth limit own parent) callbackSeed).2
        (tuplePlan (nodePlan limit own innerHeight) innerCount innerBound innerMass
          (identity_actual_frame_plan recursiveDepth limit own frame) innerSeed).2 ∧
      (tuplePlan (nodePlan limit own parentHeight) remainingCount parentBound callbackMass
        (identity_actual_frame_plan recursiveDepth limit own parent) callbackSeed).1 ⊆
        (tuplePlan (nodePlan limit own innerHeight) innerCount innerBound innerMass
          (identity_actual_frame_plan recursiveDepth limit own frame) innerSeed).1) ∧
    ((identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv frame).1
      fragments reached saved after =
      SourcePruningEnumerationSharedEagerChildren.consumeSelected
        (identity_actual_parent_tail checkEmpty edgesOf workFuel
          (identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv parent)
          completedPrefix rest)
        caller queries (.complete fragment reached saved returned)) ∧
    ∃ (next : Inventory) (final : Memos),
      SourceCurrentAllocatedPartialInvariant.Post formulas solver next original reached final ∧
      final.query = saved ∧ Packet formulas solver next reached final metadata returned ∧
      SourceEqualityRequiredCache.Keeps original.checked.native.machine.heap reached.checked.native.machine.heap := by
  let frame : IdentityActualCallbackFrame bits := .selected parent completedPrefix rest edge residual caller queries
    parentHeight remainingCount parentBound
  let callbackSeed := advance innerSeed (innerCount * (innerBound + 1))
  let callbackMass := innerMass + innerCount * innerBound
  let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
  let returned := SelectedEdge.finish residual fragment after
  have sourcePacket : ∃ (inventory : Inventory) (memos : Memos),
      Packet formulas solver inventory caller memos metadata before := by
    obtain ⟨inventory, memos, _post, _query, packet, _rest⟩ := previous
    exact ⟨inventory, memos, packet⟩
  obtain ⟨inventory, memos, packet⟩ := sourcePacket
  have head : ChildInputs formulas solver caller metadata before scs fragment reached saved returned :=
    identity_observed_own_tuple_child_inputs formulas solver inventory caller memos metadata before scs edge residual
      middle staged packet prepared fragments reached saved after history
  have outerPrefix := tuple_inputs_extend_current_head formulas solver original metadata scopeBefore
    inputs completedPrefix caller queries before incoming scs fragment reached saved returned previous member pending head
  have callbackFits : Fits callbackSeed.2 reached.checked := currentFits.mono
    (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge innerSeed (innerCount * (innerBound + 1)))
  have callbackKnown : Heap (fun guard => guard ∈ callbackSeed.1) reached.checked.native.machine.heap := by
    intro key row found
    exact (SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge innerSeed
      (innerCount * (innerBound + 1))) (currentKnown key row found)
  have callbackMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound returned.core ≤ callbackMass := by
    change SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ innerMass + innerCount * innerBound
    exact Nat.le_trans currentMass (Nat.le_add_right _ _)
  have tailReserved : tupleReserved (nodePlan limit own parentHeight) (nodeReserved bits limit own parentHeight)
      remainingCount parentBound callbackMass
      (identity_actual_frame_plan recursiveDepth limit own parent)
      (identity_actual_frame_reserved bits recursiveDepth limit own parent) callbackSeed :=
    tupleReserved_first_callback bits limit own innerHeight innerCount innerBound innerMass
      (identity_actual_frame_plan recursiveDepth limit own frame)
      (identity_actual_frame_reserved bits recursiveDepth limit own frame) innerSeed reserved
  have forecast := first_callback_le_tuple_of_growth limit own innerHeight innerCount innerBound innerMass
    (identity_actual_frame_plan recursiveDepth limit own frame)
    (identity_actual_frame_plan_ge recursiveDepth limit own frame) innerSeed
  have endpoint : ∃ (next : Inventory) (final : Memos),
      SourceCurrentAllocatedPartialInvariant.Post formulas solver next original reached final ∧
      final.query = saved ∧ Packet formulas solver next reached final metadata returned ∧
      SourceEqualityRequiredCache.Keeps original.checked.native.machine.heap reached.checked.native.machine.heap := by
    obtain ⟨next, final, post, query, afterPacket, _remaining⟩ := outerPrefix
    exact ⟨next, final, post, query, afterPacket, post.effects.keeps⟩
  exact ⟨head, outerPrefix, callbackFits, callbackKnown, callbackMassBound, counted, tailReserved,
    forecast, rfl, endpoint⟩

end ActualCallbackFrameHandoff
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualSelectedFrameGeneration
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)
local notation "Done" => List Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Stopped" => List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold
local notation "ChildDone" => Fragment → Caller (bits + 2) → Queries → Cached → Fold
local notation "Visitor" => List Suspended → Node → Caller (bits + 2) → Cached → Queries → ChildDone →
  (ChildDispatch.Observation (bits + 2) → Option Cached → Fold) → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the exact eager child's ordinary-height guard at the same work budget. -/
private noncomputable def identity_actual_guarded_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint)) (workFuel : Nat)
    (parent : Node) : Visitor :=
  fun bucket child current cache queries yes no =>
    if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent then
      SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        workFuel workFuel workFuel workFuel workFuel edgesOf bucket child current cache queries yes no
    else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty
      workFuel workFuel workFuel workFuel workFuel bucket child current cache queries yes no

/-- Actual strictly smaller row children use the same eager backend at every callback. -/
private theorem identity_actual_guarded_children_eq
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint)) (workFuel : Nat)
    (parent : Node) (inputs : List (Node × List Suspended))
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
    (lower : ∀ child bucket, (child, bucket) ∈ inputs →
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent) :
    SourcePruningEnumerationSharedChildVisitors.visitChildren
      (identity_actual_guarded_child checkEmpty edgesOf workFuel parent) done stopped inputs caller before queries =
    SourcePruningEnumerationSharedChildVisitors.visitChildren
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        workFuel workFuel workFuel workFuel workFuel edgesOf) done stopped inputs caller before queries := by
  revert lower
  induction inputs generalizing caller before queries done stopped with
  | nil =>
      intro _lower
      rfl
  | cons input rest ih =>
      intro lower
      let leftYes : ChildDone := fun fragment reached saved after =>
        SourcePruningEnumerationSharedChildVisitors.visitChildren
          (identity_actual_guarded_child checkEmpty edgesOf workFuel parent)
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved
      let rightYes : ChildDone := fun fragment reached saved after =>
        SourcePruningEnumerationSharedChildVisitors.visitChildren
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf)
          (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved
      have yesSame : leftYes = rightYes := by
        funext fragment reached saved after
        exact ih (caller := reached) (before := after) (queries := saved)
          (done := fun fragments => done (fragment :: fragments))
          (stopped := fun completed => stopped (fragment :: completed))
          (fun child bucket member => lower child bucket (List.mem_cons_of_mem input member))
      have headSource : identity_actual_guarded_child checkEmpty edgesOf workFuel parent
          input.2 input.1 caller before queries leftYes (fun observation candidate => stopped [] observation candidate) =
          SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf input.2 input.1 caller before queries
            leftYes (fun observation candidate => stopped [] observation candidate) := by
        unfold identity_actual_guarded_child
        split
        · rfl
        · rename_i notLower
          exact (notLower (lower input.1 input.2 List.mem_cons_self)).elim
      change identity_actual_guarded_child checkEmpty edgesOf workFuel parent
          input.2 input.1 caller before queries leftYes (fun observation candidate => stopped [] observation candidate) =
          SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            workFuel workFuel workFuel workFuel workFuel edgesOf input.2 input.1 caller before queries
            rightYes (fun observation candidate => stopped [] observation candidate)
      rw [headSource, yesSame]

/-- The actual general selected row generates its literal nested callback frame. -/
private theorem identity_selected_frame_generation
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (parent : IdentityActualCallbackFrame bits)
    (completedPrefix : List Fragment) (rest : List (Node × List Suspended))
    (row : EdgeValue Symbol Constraint) (residual : Option Constraint)
    (parentValue : Node) (scs : List Suspended) (caller : Caller (bits + 2)) (queries : Queries)
    (before middle : Cached) (parentHeight remainingCount parentBound : Nat)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs row before =
      some [((row.entry.key.symbol, staged, residual), middle)])
    (lower : ∀ child bucket, (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parentValue) :
    let inherited := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv parent
    let tail := identity_actual_parent_tail checkEmpty edgesOf workFuel inherited completedPrefix rest
    let frame := IdentityActualCallbackFrame.selected parent completedPrefix rest row residual caller queries
      parentHeight remainingCount parentBound
    let callbacks := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv frame
    SourcePruningEnumerationSharedChildVisitors.visitSelected
      (identity_actual_guarded_child checkEmpty edgesOf workFuel parentValue)
      (SourcePruningEnumerationSharedEagerChildren.consumeSelected tail caller queries)
      scs row caller before queries =
    SourcePruningEnumerationSharedChildVisitors.visitChildren
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        workFuel workFuel workFuel workFuel workFuel edgesOf) callbacks.1 callbacks.2
      (staged.map (fun input => (input.1, input.2.1))) caller middle queries := by
  dsimp only
  rw [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
  exact identity_actual_guarded_children_eq checkEmpty edgesOf workFuel parentValue
    (staged.map (fun input => (input.1, input.2.1))) caller middle queries
    (identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.selected parent completedPrefix rest row residual caller queries parentHeight remainingCount parentBound)).1
    (identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.selected parent completedPrefix rest row residual caller queries parentHeight remainingCount parentBound)).2 lower

end ActualSelectedFrameGeneration
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualCapturedFrameCurrentResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish emitted)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual root frame derives its callback resources from the current inner budget. -/
private theorem identity_captured_frame_current_resources
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv handle : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workerIH : IdentityEagerEmittedCompleteAtDepth (bits := bits) graph checkEmpty edgesOf formulas solver recursiveDepth)
    (inventory : Inventory) (capturedCaller : Caller (bits + 2)) (memos : Memos)
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (ownCache : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (packet : Packet formulas solver inventory capturedCaller memos metadata capturedBefore)
    (ready : EnumerationDriver.Ready uv capturedBefore.core)
    (stored : capturedBefore.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv capturedBefore.core)
    (prepared : SourcePruningEnumerationCachedOwn.prepare capturedCaller.checked.native.machine.heap scs edge capturedBefore =
      some [((edge.entry.key.symbol, staged, residual), ownCache)])
    (fragments : List Fragment) (caller : Caller (bits + 2)) (queries : Queries) (current : Cached)
    (history : TupleInputs formulas solver capturedCaller metadata ownCache
      (staged.map (fun input => (input.1, input.2.1))) fragments caller queries current)
    (limit own height unusedCount bound retainedMass : Nat) (currentSeed : Seed)
    (currentFits : Fits currentSeed.2 caller.checked)
    (currentKnown : Heap (fun guard => guard ∈ currentSeed.1) caller.checked.native.machine.heap)
    (currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound current.core ≤ retainedMass)
    (selectionMembers : ∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      unusedCount bound retainedMass (fun retained seed => eagerFinal recursiveDepth seed retained)
      (fun retained seed => eagerReserved bits recursiveDepth seed retained) currentSeed) :
    IdentityEmittedCompleteResources formulas solver capturedCaller
      (tuplePlan (nodePlan limit own height) unusedCount bound retainedMass
        (fun retained seed => eagerFinal recursiveDepth seed retained) currentSeed)
      (finish uv ((identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
        (.captured edge residual capturedCaller capturedQueries)).1 fragments caller queries current)) := by
  let callbackSeed := advance currentSeed (unusedCount * (bound + 1))
  let callbackMass := retainedMass + unusedCount * bound
  let plan := tuplePlan (nodePlan limit own height) unusedCount bound retainedMass
    (fun retained seed => eagerFinal recursiveDepth seed retained) currentSeed
  let fragment : Fragment := .node edge.entry.key.symbol fragments
  let childAfter := SelectedEdge.finish residual fragment current
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (Typing := Unit) (width := bits + 2) child
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveDepth)
    graph [] none (fun _ _ => none) workFuel metadata uv
  have callbackReserved : eagerReserved bits recursiveDepth callbackSeed callbackMass :=
    tupleReserved_first_callback bits limit own height unusedCount bound retainedMass
      (fun retained seed => eagerFinal recursiveDepth seed retained)
      (fun retained seed => eagerReserved bits recursiveDepth seed retained) currentSeed reserved
  have included := first_callback_le_tuple_of_growth limit own height unusedCount bound retainedMass
    (fun retained seed => eagerFinal recursiveDepth seed retained)
    (fun retained seed => eagerFinal_ge recursiveDepth seed retained) currentSeed
  have callbackFits : Fits callbackSeed.2 caller.checked := currentFits.mono
    (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge currentSeed (unusedCount * (bound + 1)))
  have callbackKnown : Heap (fun guard => guard ∈ callbackSeed.1) caller.checked.native.machine.heap := by
    intro key row found
    exact (SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge currentSeed
      (unusedCount * (bound + 1))) (currentKnown key row found)
  have data := identity_observed_own_tuple_child_inputs formulas solver inventory capturedCaller memos metadata
    capturedBefore scs edge residual ownCache staged packet prepared fragments caller queries current history
  have childMass : SourcePruningEnumerationPrefixAdmission.suspendedBound childAfter.core ≤ callbackMass := by
    change SourcePruningEnumerationPrefixAdmission.suspendedBound current.core ≤ retainedMass + unusedCount * bound
    exact Nat.le_trans currentMass (Nat.le_add_right _ _)
  change IdentityEmittedCompleteResources formulas solver capturedCaller plan
    (finish uv ((identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.captured edge residual capturedCaller capturedQueries)).1 fragments caller queries current))
  rw [identity_actual_frame_callbacks]
  change IdentityEmittedCompleteResources formulas solver capturedCaller plan
    (finish uv (match SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap workFuel uv fragment childAfter with
      | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook capturedCaller capturedQueries
          (some (.complete fragment caller queries finished))
      | none => SourcePruningEnumerationSharedReceiptContinuation.run hook capturedCaller capturedQueries
          (some (.finalizeStopped fragment caller queries childAfter))))
  cases observedFinish : SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap workFuel uv fragment childAfter with
  | none =>
      constructor
      · intro output member
        cases member
      · trivial
  | some finished =>
      obtain ⟨next, final, finalFuel, canonicalAfter, post, querySame, finalAt,
          finishedPacket, _fragmentBound, _core, finalMass, _stored, _root⟩ :=
        finalize_child_inputs_packet formulas solver capturedCaller caller metadata capturedBefore childAfter uv handle scs
          fragment queries ready stored incoming data
      have observedLater := SourcePruningEnumerationFinalize.run_some_moreFuel
        caller.checked.native.machine.heap workFuel finalFuel uv fragment childAfter finished observedFinish
      have canonicalLater := finalAt workFuel
      rw [Nat.add_comm workFuel finalFuel] at observedLater
      have sameCache : canonicalAfter = finished := Option.some.inj (canonicalLater.symm.trans observedLater)
      subst canonicalAfter
      have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ callbackMass :=
        Nat.le_trans finalMass childMass
      have callback := identity_callback_emitted_complete_at_any_budget graph checkEmpty edgesOf formulas solver recursiveDepth
        workerIH next caller final finished metadata uv fragment callbackSeed callbackMass finishedPacket callbackFits callbackKnown
        selectionMembers selectionLength actualMass callbackReserved workFuel
      rw [querySame] at callback
      have enlarged := identity_emitted_complete_mono included.1 included.2 callback
      have framed := identity_emitted_complete_post post enlarged
      have actualHook : IdentityEmittedCompleteResources formulas solver capturedCaller plan
          (hook fragment caller queries finished) := by
        simpa only [hook, child] using framed
      cases observedHook : hook fragment caller queries finished with
      | complete outputs reached saved =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish] using actualHook
      | stopped outputs reason endpoint =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish,
            IdentityEmittedCompleteResources, emitted] using actualHook

end ActualCapturedFrameCurrentResources
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualFrameReturnSteps
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}

/-- Count the remaining child calls and the deferred actual continuation. -/
private def identity_actual_tuple_steps (child : Nat → Nat) : Nat → Nat → Nat
  | 0, continuation => continuation + 1
  | count + 1, continuation => child (identity_actual_tuple_steps child count continuation) + 1

/-- Count the fallback and all bounded row attempts, including deferred tails. -/
private def identity_actual_node_steps (limit : Nat) : Nat → Nat → Nat
  | 0, continuation => continuation + 1
  | height + 1, continuation => continuation + 2 +
      (limit + 1) * (identity_actual_tuple_steps (identity_actual_node_steps limit height)
        limit (continuation + 1) + 1)

/-- Every node call has room for its literal deferred continuation. -/
private theorem identity_actual_node_steps_gt (limit height continuation : Nat) :
    continuation < identity_actual_node_steps limit height continuation := by
  cases height <;> simp only [identity_actual_node_steps] <;> omega

/-- A larger tuple count includes every smaller remaining tuple. -/
private theorem identity_actual_tuple_steps_count_le
    (child : Nat → Nat) (growth : ∀ continuation, continuation < child continuation)
    (first last continuation : Nat) (within : first ≤ last) :
    identity_actual_tuple_steps child first continuation ≤
      identity_actual_tuple_steps child last continuation := by
  induction last generalizing first with
  | zero =>
      have same : first = 0 := by omega
      subst first
      exact Nat.le_refl _
  | succ last ih =>
      by_cases previous : first ≤ last
      · have smaller := ih first previous
        have next := growth (identity_actual_tuple_steps child last continuation)
        simp only [identity_actual_tuple_steps]
        omega
      · have same : first = last + 1 := by omega
        subst first
        exact Nat.le_refl _

/-- Retain every deferred ancestor tail in the actual source frame. -/
private def identity_actual_frame_steps (limit : Nat) : IdentityActualCallbackFrame bits → Nat
  | .captured _edge _residual _caller _queries => 1
  | .selected parent _completedPrefix _rest _edge _residual _caller _queries
      parentHeight remainingCount _parentBound =>
      identity_actual_tuple_steps (identity_actual_node_steps limit parentHeight)
        remainingCount (identity_actual_frame_steps limit parent) + 1

/-- The literal actual parent-tail call is smaller than its selected-row frame. -/
private theorem identity_selected_frame_return_steps
    (limit : Nat) (parent : IdentityActualCallbackFrame bits)
    (completedPrefix : List Fragment) (rest : List (Node × List Suspended))
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
    (caller : Caller (bits + 2)) (queries : Queries)
    (parentHeight remainingCount parentBound : Nat) (counted : rest.length ≤ remainingCount) :
    identity_actual_tuple_steps (identity_actual_node_steps limit parentHeight)
      rest.length (identity_actual_frame_steps limit parent) <
      identity_actual_frame_steps limit
        (.selected parent completedPrefix rest edge residual caller queries
          parentHeight remainingCount parentBound) := by
  have smaller := identity_actual_tuple_steps_count_le
    (identity_actual_node_steps limit parentHeight)
    (identity_actual_node_steps_gt limit parentHeight)
    rest.length remainingCount (identity_actual_frame_steps limit parent) counted
  change identity_actual_tuple_steps (identity_actual_node_steps limit parentHeight)
      rest.length (identity_actual_frame_steps limit parent) <
    identity_actual_tuple_steps (identity_actual_node_steps limit parentHeight)
      remainingCount (identity_actual_frame_steps limit parent) + 1
  omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The exact selected callback invokes this smaller actual parent-tail task. -/
private theorem identity_selected_frame_actual_smaller_return
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel limit : Nat)
    (metadata : Metadata Unit) (uv : Nat) (parent : IdentityActualCallbackFrame bits)
    (completedPrefix : List Fragment) (rest : List (Node × List Suspended))
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
    (caller : Caller (bits + 2)) (queries : Queries) (parentHeight remainingCount parentBound : Nat)
    (fragments : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (counted : rest.length ≤ remainingCount) :
    let frame := IdentityActualCallbackFrame.selected parent completedPrefix rest edge residual caller queries
      parentHeight remainingCount parentBound
    let inherited := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv parent
    let tail := identity_actual_parent_tail checkEmpty edgesOf workFuel inherited completedPrefix rest
    let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
    let returned := SelectedEdge.finish residual fragment after
    (identity_actual_tuple_steps (identity_actual_node_steps limit parentHeight)
      rest.length (identity_actual_frame_steps limit parent) < identity_actual_frame_steps limit frame) ∧
    ((identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv frame).1
      fragments reached saved after =
      match tail fragment reached saved returned with
      | .complete processed outputs finalCaller finalQueries =>
          .complete (.complete fragment reached saved returned :: processed) outputs finalCaller finalQueries
      | .stopped processed outputs current =>
          .stopped (.complete fragment reached saved returned :: processed) outputs current) := by
  constructor
  · exact identity_selected_frame_return_steps limit parent completedPrefix rest edge residual
      caller queries parentHeight remainingCount parentBound counted
  · exact identity_selected_frame_callback graph checkEmpty edgesOf recursiveDepth workFuel metadata uv parent
      completedPrefix rest edge residual caller queries parentHeight remainingCount parentBound
      fragments reached saved after

end ActualFrameReturnSteps
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualCapturedFrameCurrentLocalResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish emitted)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual root callback retains the Post from its current entry caller. -/
private theorem identity_captured_frame_current_local_resources
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv handle : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workerIH : IdentityEagerEmittedCompleteAtDepth (bits := bits) graph checkEmpty edgesOf formulas solver recursiveDepth)
    (inventory : Inventory) (capturedCaller : Caller (bits + 2)) (memos : Memos)
    (capturedQueries : Queries) (capturedBefore : Cached) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint) (ownCache : Cached)
    (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (packet : Packet formulas solver inventory capturedCaller memos metadata capturedBefore)
    (ready : EnumerationDriver.Ready uv capturedBefore.core)
    (stored : capturedBefore.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv capturedBefore.core)
    (prepared : SourcePruningEnumerationCachedOwn.prepare capturedCaller.checked.native.machine.heap scs edge capturedBefore =
      some [((edge.entry.key.symbol, staged, residual), ownCache)])
    (fragments : List Fragment) (caller : Caller (bits + 2)) (queries : Queries) (current : Cached)
    (history : TupleInputs formulas solver capturedCaller metadata ownCache
      (staged.map (fun input => (input.1, input.2.1))) fragments caller queries current)
    (limit own height unusedCount bound retainedMass : Nat) (currentSeed : Seed)
    (currentFits : Fits currentSeed.2 caller.checked)
    (currentKnown : Heap (fun guard => guard ∈ currentSeed.1) caller.checked.native.machine.heap)
    (currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound current.core ≤ retainedMass)
    (selectionMembers : ∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      unusedCount bound retainedMass (fun retained seed => eagerFinal recursiveDepth seed retained)
      (fun retained seed => eagerReserved bits recursiveDepth seed retained) currentSeed) :
    IdentityEmittedCompleteResources formulas solver caller
      (tuplePlan (nodePlan limit own height) unusedCount bound retainedMass
        (fun retained seed => eagerFinal recursiveDepth seed retained) currentSeed)
      (finish uv ((identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
        (.captured edge residual capturedCaller capturedQueries)).1 fragments caller queries current)) := by
  let callbackSeed := advance currentSeed (unusedCount * (bound + 1))
  let callbackMass := retainedMass + unusedCount * bound
  let plan := tuplePlan (nodePlan limit own height) unusedCount bound retainedMass
    (fun retained seed => eagerFinal recursiveDepth seed retained) currentSeed
  let fragment : Fragment := .node edge.entry.key.symbol fragments
  let childAfter := SelectedEdge.finish residual fragment current
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (Typing := Unit) (width := bits + 2) child
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveDepth)
    graph [] none (fun _ _ => none) workFuel metadata uv
  have callbackReserved : eagerReserved bits recursiveDepth callbackSeed callbackMass :=
    tupleReserved_first_callback bits limit own height unusedCount bound retainedMass
      (fun retained seed => eagerFinal recursiveDepth seed retained)
      (fun retained seed => eagerReserved bits recursiveDepth seed retained) currentSeed reserved
  have included := first_callback_le_tuple_of_growth limit own height unusedCount bound retainedMass
    (fun retained seed => eagerFinal recursiveDepth seed retained)
    (fun retained seed => eagerFinal_ge recursiveDepth seed retained) currentSeed
  have callbackFits : Fits callbackSeed.2 caller.checked := currentFits.mono
    (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge currentSeed (unusedCount * (bound + 1)))
  have callbackKnown : Heap (fun guard => guard ∈ callbackSeed.1) caller.checked.native.machine.heap := by
    intro key row found
    exact (SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge currentSeed
      (unusedCount * (bound + 1))) (currentKnown key row found)
  have data := identity_observed_own_tuple_child_inputs formulas solver inventory capturedCaller memos metadata
    capturedBefore scs edge residual ownCache staged packet prepared fragments caller queries current history
  have childMass : SourcePruningEnumerationPrefixAdmission.suspendedBound childAfter.core ≤ callbackMass := by
    change SourcePruningEnumerationPrefixAdmission.suspendedBound current.core ≤ retainedMass + unusedCount * bound
    exact Nat.le_trans currentMass (Nat.le_add_right _ _)
  change IdentityEmittedCompleteResources formulas solver caller plan
    (finish uv ((identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.captured edge residual capturedCaller capturedQueries)).1 fragments caller queries current))
  rw [identity_actual_frame_callbacks]
  change IdentityEmittedCompleteResources formulas solver caller plan
    (finish uv (match SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap workFuel uv fragment childAfter with
      | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook capturedCaller capturedQueries
          (some (.complete fragment caller queries finished))
      | none => SourcePruningEnumerationSharedReceiptContinuation.run hook capturedCaller capturedQueries
          (some (.finalizeStopped fragment caller queries childAfter))))
  cases observedFinish : SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap workFuel uv fragment childAfter with
  | none =>
      constructor
      · intro output member
        cases member
      · trivial
  | some finished =>
      obtain ⟨next, final, finalFuel, canonicalAfter, _post, querySame, finalAt,
          finishedPacket, _fragmentBound, _core, finalMass, _stored, _root⟩ :=
        finalize_child_inputs_packet formulas solver capturedCaller caller metadata capturedBefore childAfter uv handle scs
          fragment queries ready stored incoming data
      have observedLater := SourcePruningEnumerationFinalize.run_some_moreFuel
        caller.checked.native.machine.heap workFuel finalFuel uv fragment childAfter finished observedFinish
      have canonicalLater := finalAt workFuel
      rw [Nat.add_comm workFuel finalFuel] at observedLater
      have sameCache : canonicalAfter = finished := Option.some.inj (canonicalLater.symm.trans observedLater)
      subst canonicalAfter
      have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ callbackMass :=
        Nat.le_trans finalMass childMass
      have callback := identity_callback_emitted_complete_at_any_budget graph checkEmpty edgesOf formulas solver recursiveDepth
        workerIH next caller final finished metadata uv fragment callbackSeed callbackMass finishedPacket callbackFits callbackKnown
        selectionMembers selectionLength actualMass callbackReserved workFuel
      rw [querySame] at callback
      have enlarged := identity_emitted_complete_mono included.1 included.2 callback
      have actualHook : IdentityEmittedCompleteResources formulas solver caller plan
          (hook fragment caller queries finished) := by
        simpa only [hook, child] using enlarged
      cases observedHook : hook fragment caller queries finished with
      | complete outputs reached saved =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish] using actualHook
      | stopped outputs reason endpoint =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, observedHook, finish,
            IdentityEmittedCompleteResources, emitted] using actualHook

end ActualCapturedFrameCurrentLocalResources
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualTupleCapturedNativePost
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual native Post retains the full prefix in its restored captured cache. -/
private theorem tuple_inputs_captured_native_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (scopeBefore : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller reached : Caller (bits + 2)) (queries saved : Queries) (captured : Cached)
    (next : Inventory) (final : Memos)
    (previous : TupleInputs formulas solver original metadata scopeBefore inputs completed caller queries captured)
    (post : SourceCurrentAllocatedPartialInvariant.Post formulas solver next caller reached final)
    (querySame : final.query = saved) :
    TupleInputs formulas solver original metadata scopeBefore inputs completed reached saved captured := by
  obtain ⟨_inventory, _memos, previousPost, _previousQuery, packet, remaining⟩ := previous
  exact ⟨next, final, previousPost.trans post, querySame,
    SourcePruningEnumerationRecursive.captured_post packet post, remaining⟩

end ActualTupleCapturedNativePost
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualSourceOriginAndForwardCons
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (iterate)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
local notation "Fold" => NativeContinuations.Result
  (Output (bits + 2) Unit) (Failure (bits + 2) Unit) (bits + 2)

/-- Retain the original prepared scope without any later native resource field. -/
private structure IdentityActualSourceRoot (bits : Nat) where
  caller : Caller (bits + 2)
  queries : Queries
  before : Cached
  incoming : Node
  scs : List Suspended
  rawSeed : Seed
  ceiling : Nat

private def IdentityActualSourceRoot.start (root : IdentityActualSourceRoot bits) : Seed :=
  SourcePruningEnumerationSharedPreparedReservation.preparedSeed root.rawSeed
private def IdentityActualSourceRoot.limit (root : IdentityActualSourceRoot bits) : Nat :=
  SourceCurrentConstrainedCapTargetForecast.scalar root.start.2
private noncomputable def IdentityActualSourceRoot.own (root : IdentityActualSourceRoot bits) : Nat :=
  SourcePruningEnumerationGuardWidth.width root.start.1

/-- Compute each row boundary from the original prepared scope. -/
private noncomputable def IdentityActualSourceRoot.rowSeed
    (root : IdentityActualSourceRoot bits) (recursiveDepth index : Nat) : Seed :=
  let continuation := fun retained current => eagerFinal recursiveDepth current retained
  iterate (fun current => tuplePlan (nodePlan root.limit root.own (root.limit - 1))
    root.limit (root.ceiling + root.own) root.ceiling continuation current)
    (fallbackPlan root.ceiling root.ceiling continuation root.start) index

/-- Source bounds remain about the original captured heap and computed seed. -/
private def IdentityActualSourceRoot.Shapes (root : IdentityActualSourceRoot bits) : Prop :=
  (∀ value, Available root.caller.checked.native.machine.heap value →
    MergedOrdinaryHeight.height value ≤ root.limit) ∧
  ∀ entry rows depth free,
    Available root.caller.checked.native.machine.heap (.node entry rows depth free) →
    rows.length ≤ root.limit ∧ ∀ edge ∈ rows, edge.children.length ≤ root.limit ∧
      ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint =
        some (tries, residual) → tries.length ≤ root.own

/-- Store only actual source data and its mathematical current position. -/
private structure IdentityActualSourcePoint (bits : Nat) where
  frame : IdentityActualCallbackFrame bits
  completed : List Fragment
  caller : Caller (bits + 2)
  before : Cached
  queries : Queries
  height : Nat
  count : Nat
  bound : Nat
  mass : Nat
  seed : Seed

/-- Distinguish the literal tuple, head child and ordinary scan operations. -/
private inductive IdentityActualSourceTask (bits : Nat) where
  | tuple (point : IdentityActualSourcePoint bits) (remaining : List (Node × List Suspended))
  | child (point : IdentityActualSourcePoint bits) (incoming : Node) (bucket : List Suspended)
      (rest : List (Node × List Suspended))
  | rows (height : Nat) (point : IdentityActualSourcePoint bits) (incoming : Node)
      (bucket : List Suspended) (rest : List (Node × List Suspended))

private def IdentityActualSourceTask.point : IdentityActualSourceTask bits → IdentityActualSourcePoint bits
  | .tuple point _ => point
  | .child point _ _ _ => point
  | .rows _ point _ _ _ => point
private def IdentityActualSourceTask.inputs : IdentityActualSourceTask bits → List (Node × List Suspended)
  | .tuple _ remaining => remaining
  | .child _ incoming bucket rest => (incoming, bucket) :: rest
  | .rows _ _ incoming bucket rest => (incoming, bucket) :: rest
private def IdentityActualSourceTask.capacity : IdentityActualSourceTask bits → Nat
  | .tuple point _ => point.count
  | .child point _ _ _ => point.count + 1
  | .rows _ point _ _ _ => point.count + 1

/-- Count the deferred tail by its source-plan count bound. -/
private def IdentityActualSourcePoint.tailSteps (limit : Nat) (point : IdentityActualSourcePoint bits) : Nat :=
  identity_actual_tuple_steps (identity_actual_node_steps limit point.height)
    point.count (identity_actual_frame_steps limit point.frame)

private def IdentityActualSourceTask.work (limit : Nat) : IdentityActualSourceTask bits → Nat
  | .tuple point _ => point.tailSteps limit
  | .child point _ _ _ => identity_actual_node_steps limit point.height (point.tailSteps limit)
  | .rows height point _ _ _ => (limit + 1) *
      (identity_actual_tuple_steps (identity_actual_node_steps limit height)
        limit (point.tailSteps limit + 1) + 1)

private noncomputable def IdentityActualSourcePoint.tailPlan
    (recursiveDepth limit own : Nat) (point : IdentityActualSourcePoint bits) : Nat → Seed → Seed :=
  fun retained current => tuplePlan (nodePlan limit own point.height) point.count point.bound retained
    (identity_actual_frame_plan recursiveDepth limit own point.frame) current
private noncomputable def IdentityActualSourcePoint.tailReserved
    (recursiveDepth limit own : Nat) (point : IdentityActualSourcePoint bits) : Nat → Seed → Prop :=
  fun retained current => tupleReserved (nodePlan limit own point.height) (nodeReserved bits limit own point.height)
    point.count point.bound retained (identity_actual_frame_plan recursiveDepth limit own point.frame)
    (identity_actual_frame_reserved bits recursiveDepth limit own point.frame) current

private noncomputable def IdentityActualSourceTask.entrySeed (recursiveDepth limit own : Nat) :
    IdentityActualSourceTask bits → Seed
  | .tuple point _ => point.seed
  | .child point _ _ _ => point.seed
  | .rows _ point _ _ _ => fallbackPlan point.bound point.mass
      (point.tailPlan recursiveDepth limit own) point.seed

private noncomputable def IdentityActualSourceTask.goal (recursiveDepth limit own : Nat) :
    IdentityActualSourceTask bits → IdentityReservationGoal
  | .tuple point _ => .tuple limit own point.height point.count point.bound point.mass
      (identity_actual_frame_plan recursiveDepth limit own point.frame)
      (identity_actual_frame_reserved bits recursiveDepth limit own point.frame) point.seed
  | .child point _ _ _ => .node limit own point.height point.bound point.mass
      (point.tailPlan recursiveDepth limit own) (point.tailReserved recursiveDepth limit own) point.seed
  | .rows height point _ _ _ => .rows limit own height limit point.bound point.mass
      (point.tailPlan recursiveDepth limit own) (point.tailReserved recursiveDepth limit own)
      (fallbackPlan point.bound point.mass (point.tailPlan recursiveDepth limit own) point.seed)

/-- Keep the row boundary in the original fixed ordinary-child forecast. -/
private noncomputable def identity_actual_source_row_boundary
    (recursiveDepth limit own height : Nat) (point : IdentityActualSourcePoint bits) (index : Nat) : Seed :=
  iterate (fun current => tuplePlan (nodePlan limit own height)
    limit (point.bound + own) point.mass (point.tailPlan recursiveDepth limit own) current)
    (fallbackPlan point.bound point.mass (point.tailPlan recursiveDepth limit own) point.seed) index

/-- A selected row starts a new local scope and retains its actual parent tail. -/
private def identity_actual_source_inner_point
    (height limit own : Nat) (point : IdentityActualSourcePoint bits)
    (rest : List (Node × List Suspended)) (edge : EdgeValue Symbol Constraint)
    (residual : Option Constraint) (caller : Caller (bits + 2)) (queries : Queries)
    (rowOwn : Cached) (rowSeed : Seed) : IdentityActualSourcePoint bits := {
  frame := .selected point.frame point.completed rest edge residual caller queries
    point.height point.count point.bound
  completed := []
  caller := caller
  before := rowOwn
  queries := queries
  height := height
  count := limit
  bound := point.bound + own
  mass := point.mass
  seed := rowSeed }

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Interpret only the literal optimized operations and deferred source frame. -/
private noncomputable def IdentityActualSourceTask.run
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) : IdentityActualSourceTask bits → Fold
  | .tuple point remaining =>
      let callbacks := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv point.frame
      SourcePruningEnumerationSharedChildVisitors.visitChildren
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          workFuel workFuel workFuel workFuel workFuel edgesOf)
        (fun fragments => callbacks.1 (point.completed ++ fragments))
        (fun completedTail => callbacks.2 (point.completed ++ completedTail))
        remaining point.caller point.before point.queries
  | .child point incoming bucket rest =>
      let callbacks := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv point.frame
      SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        workFuel workFuel workFuel workFuel workFuel edgesOf bucket incoming point.caller point.before point.queries
        (identity_actual_parent_tail checkEmpty edgesOf workFuel callbacks point.completed rest)
        (callbacks.2 point.completed)
  | .rows _ point incoming bucket rest =>
      let callbacks := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv point.frame
      let tail := identity_actual_parent_tail checkEmpty edgesOf workFuel callbacks point.completed rest
      SourcePruningEnumerationSharedBranching.scan
        (fun edge reached saved captured => SourcePruningEnumerationSharedChildVisitors.visitSelected
          (identity_actual_guarded_child checkEmpty edgesOf workFuel incoming)
          (SourcePruningEnumerationSharedEagerChildren.consumeSelected tail reached saved)
          bucket edge reached captured saved)
        point.before (edgesOf incoming) point.caller point.queries

private noncomputable def identity_actual_source_root_visit
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (scs : List Suspended) :
    EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold :=
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Unit) (Reason := Failure (bits + 2) Unit)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (Typing := Unit) (width := bits + 2)
      child (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf none
      (fun _ _ => none) workFuel recursiveDepth)
    graph [] none (fun _ _ => none) workFuel metadata uv
  SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook workFuel uv scs

/-- Execute only the literal earlier ordinary rows at their shared native endpoints. -/
private noncomputable def identity_actual_source_row_prefix_run
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (point : IdentityActualSourcePoint bits)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (attempted : List (EdgeValue Symbol Constraint)) : Fold :=
  let callbacks := identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv point.frame
  let tail := identity_actual_parent_tail checkEmpty edgesOf workFuel callbacks point.completed rest
  SourcePruningEnumerationSharedBranching.scan
    (fun edge reached saved captured => SourcePruningEnumerationSharedChildVisitors.visitSelected
      (identity_actual_guarded_child checkEmpty edgesOf workFuel incoming)
      (SourcePruningEnumerationSharedEagerChildren.consumeSelected tail reached saved)
      bucket edge reached captured saved)
    point.before attempted point.caller point.queries

/-- Generate task origins from literal past calls, without native resource providers. -/
private inductive IdentityActualSourceOrigin
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (root : IdentityActualSourceRoot bits) :
    IdentityActualSourceTask bits → Prop where
  | capturedTuple (attempted remaining : List (EdgeValue Symbol Constraint))
      (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
      (processed : List (SelectedEdge.Result (bits + 2))) (outputs : List (Output (bits + 2) Unit))
      (caller : Caller (bits + 2)) (queries : Queries) (ownCache : Cached)
      (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
      (selected : edgesOf root.incoming = attempted ++ edge :: remaining)
      (past : SourcePruningEnumerationSharedBranching.scan
        (identity_actual_source_root_visit graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root.scs)
        root.before attempted root.caller root.queries = .complete processed outputs caller queries)
      (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap root.scs edge root.before =
        some [((edge.entry.key.symbol, staged, residual), ownCache)]) :
      IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.tuple {
          frame := .captured edge residual caller queries
          completed := []
          caller := caller
          before := ownCache
          queries := queries
          height := root.limit - 1
          count := root.limit
          bound := root.ceiling + root.own
          mass := root.ceiling
          seed := root.rowSeed recursiveDepth attempted.length }
          (staged.map (fun input => (input.1, input.2.1))))
  | tupleHead (point : IdentityActualSourcePoint bits) (count : Nat)
      (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
      (origin : IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.tuple {point with count := count + 1} ((incoming, bucket) :: rest))) :
      IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.child {point with count := count} incoming bucket rest)
  | ordinaryRows (point : IdentityActualSourcePoint bits) (height : Nat)
      (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
      (origin : IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.child {point with height := height + 1} incoming bucket rest))
      (ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = true) :
      IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.rows height {point with height := height + 1} incoming bucket rest)

  | selectedOwn (point : IdentityActualSourcePoint bits) (height : Nat)
      (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
      (bucket : List Suspended) (rest : List (Node × List Suspended))
      (attempted remaining : List (EdgeValue Symbol Constraint))
      (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
      (processed : List (SelectedEdge.Result (bits + 2))) (outputs : List (Output (bits + 2) Unit))
      (caller : Caller (bits + 2)) (queries : Queries) (rowOwn : Cached)
      (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
      (origin : IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.rows height {point with height := height + 1} (.node parentEntry rows depth free) bucket rest))
      (sourceRows : edgesOf (.node parentEntry rows depth free) = attempted ++ edge :: remaining)
      (selected : edge ∈ rows)
      (past : identity_actual_source_row_prefix_run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
        {point with height := height + 1} (.node parentEntry rows depth free) bucket rest attempted =
          .complete processed outputs caller queries)
      (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket edge point.before =
        some [((edge.entry.key.symbol, staged, residual), rowOwn)])
      (lower : ∀ child scs, (child, scs) ∈ staged.map (fun input => (input.1, input.2.1)) →
        MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free)) :
      IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.tuple (identity_actual_source_inner_point height root.limit root.own {point with height := height + 1}
          rest edge residual caller queries rowOwn
          (identity_actual_source_row_boundary recursiveDepth root.limit root.own height
            {point with height := height + 1} attempted.length))
          (staged.map (fun input => (input.1, input.2.1))))

/-- Current facts concern the reached prefix, not any future callback result. -/
private def IdentityActualSourcePoint.Inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (root : IdentityActualSourceRoot bits) (original : Caller (bits + 2)) (metadata : Metadata Unit)
    (scopeBefore : Cached) (allInputs : List (Node × List Suspended))
    (point : IdentityActualSourcePoint bits) (inputs : List (Node × List Suspended)) (capacity : Nat) : Prop :=
  root.Shapes ∧
  SourceEqualityRequiredCache.Keeps root.caller.checked.native.machine.heap point.caller.checked.native.machine.heap ∧
  ∃ (inventory : Inventory) (memos : Memos),
    Packet formulas solver inventory point.caller memos metadata point.before ∧
    memos.query = point.queries ∧
    TupleInputs formulas solver original metadata scopeBefore allInputs point.completed
      point.caller point.queries point.before ∧
    SourcePruningEnumerationPrefixAdmission.suspendedBound point.before.core ≤ point.mass ∧
    inputs.length ≤ capacity ∧ inputs ⊆ allInputs ∧
    ∀ child bucket, (child, bucket) ∈ inputs →
      Available root.caller.checked.native.machine.heap child ∧ child.free = [] ∧
      MergedOrdinaryHeight.height child ≤ point.height ∧ bucket.length ≤ point.bound ∧
      (∀ sc ∈ bucket, sc.var < point.before.core.counter) ∧ InputsPending point.before.core bucket

private noncomputable def IdentityActualSourceCurrent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (root : IdentityActualSourceRoot bits) (original : Caller (bits + 2)) (metadata : Metadata Unit)
    (scopeBefore : Cached) (allInputs : List (Node × List Suspended)) (recursiveDepth : Nat)
    (task : IdentityActualSourceTask bits) : Prop :=
  task.point.Inputs formulas solver root original metadata scopeBefore allInputs task.inputs task.capacity ∧
  Fits (task.entrySeed recursiveDepth root.limit root.own).2 task.point.caller.checked ∧
  Heap (fun guard => guard ∈ (task.entrySeed recursiveDepth root.limit root.own).1)
    task.point.caller.checked.native.machine.heap ∧
  (task.goal recursiveDepth root.limit root.own).reserved bits

/-- The actual tuple cons enters its head child at the same native endpoint. -/
private theorem identity_actual_source_tuple_cons_run
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (point : IdentityActualSourcePoint bits) (count : Nat)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended)) :
    IdentityActualSourceTask.run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.tuple {point with count := count + 1} ((incoming, bucket) :: rest)) =
    IdentityActualSourceTask.run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.child {point with count := count} incoming bucket rest) := by
  simp only [IdentityActualSourceTask.run, SourcePruningEnumerationSharedChildVisitors.visitChildren,
    List.append_nil] <;> rfl

/-- The source ordinary branch is its literal guarded ordered scan. -/
private theorem identity_actual_source_ordinary_run
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (point : IdentityActualSourcePoint bits) (height : Nat)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = true) :
    IdentityActualSourceTask.run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.child {point with height := height + 1} incoming bucket rest) =
    IdentityActualSourceTask.run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.rows height {point with height := height + 1} incoming bucket rest) := by
  dsimp only [IdentityActualSourceTask.run]
  rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary _ _ _ _ _ _ _ _ _ _ _ _ _ _ ordinary] <;> rfl

/-- Cons preserves the produced current facts and decreases work with the same deferred bound. -/
private theorem identity_actual_source_cons_current
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (root : IdentityActualSourceRoot bits) (original : Caller (bits + 2))
    (scopeBefore : Cached) (allInputs : List (Node × List Suspended))
    (point : IdentityActualSourcePoint bits) (count : Nat)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (origin : IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
      (.tuple {point with count := count + 1} ((incoming, bucket) :: rest)))
    (current : IdentityActualSourceCurrent formulas solver root original metadata scopeBefore allInputs recursiveDepth
      (.tuple {point with count := count + 1} ((incoming, bucket) :: rest))) :
    IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
      (.child {point with count := count} incoming bucket rest) ∧
    IdentityActualSourceCurrent formulas solver root original metadata scopeBefore allInputs recursiveDepth
      (.child {point with count := count} incoming bucket rest) ∧
    IdentityActualSourceTask.work root.limit (.child {point with count := count} incoming bucket rest) <
      IdentityActualSourceTask.work root.limit
        (.tuple {point with count := count + 1} ((incoming, bucket) :: rest)) := by
  refine ⟨.tupleHead point count incoming bucket rest origin, ?_, ?_⟩
  · exact current
  · change identity_actual_node_steps root.limit point.height
        (identity_actual_tuple_steps (identity_actual_node_steps root.limit point.height)
          count (identity_actual_frame_steps root.limit point.frame)) <
      identity_actual_node_steps root.limit point.height
        (identity_actual_tuple_steps (identity_actual_node_steps root.limit point.height)
          count (identity_actual_frame_steps root.limit point.frame)) + 1
    omega

section ActualSourceOrdinaryCurrentReduction
attribute [local irreducible] fallbackPlan nodePlan tuplePlan identity_actual_frame_plan
  IdentityActualSourceRoot.own IdentityActualSourceRoot.limit

/-- Ordinary scan entry derives its padded native facts and row admission from the child entry. -/
private theorem identity_actual_source_ordinary_current
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (root : IdentityActualSourceRoot bits) (original : Caller (bits + 2))
    (scopeBefore : Cached) (allInputs : List (Node × List Suspended))
    (point : IdentityActualSourcePoint bits) (height : Nat)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (origin : IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
      (.child {point with height := height + 1} incoming bucket rest))
    (ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = true)
    (current : IdentityActualSourceCurrent formulas solver root original metadata scopeBefore allInputs recursiveDepth
      (.child {point with height := height + 1} incoming bucket rest)) :
    IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
      (.rows height {point with height := height + 1} incoming bucket rest) ∧
    IdentityActualSourceCurrent formulas solver root original metadata scopeBefore allInputs recursiveDepth
      (.rows height {point with height := height + 1} incoming bucket rest) ∧
    IdentityActualSourceTask.work root.limit (.rows height {point with height := height + 1} incoming bucket rest) <
      IdentityActualSourceTask.work root.limit (.child {point with height := height + 1} incoming bucket rest) := by
  let selected := {point with height := height + 1}
  let tail := selected.tailPlan recursiveDepth root.limit root.own
  have growth : ∀ retained seed, Le seed.2 (tail retained seed).2 ∧ seed.1 ⊆ (tail retained seed).1 := by
    intro retained seed
    exact tuplePlan_ge (nodePlan root.limit root.own selected.height)
      (nodePlan_ge root.limit root.own selected.height) selected.count selected.bound retained
      (identity_actual_frame_plan recursiveDepth root.limit root.own selected.frame)
      (identity_actual_frame_plan_ge recursiveDepth root.limit root.own selected.frame) seed
  obtain ⟨inputs, fits, known, reserved⟩ := current
  have pad := fallbackPlan_ge selected.bound selected.mass tail growth selected.seed
  refine ⟨.ordinaryRows point height incoming bucket rest origin ordinary, ?_, ?_⟩
  · refine ⟨inputs, fits.mono pad.1, ?_, ?_⟩
    · intro key row found
      exact pad.2 (known key row found)
    · exact reserved.2
  · change (root.limit + 1) *
        (identity_actual_tuple_steps (identity_actual_node_steps root.limit height)
          root.limit (selected.tailSteps root.limit + 1) + 1) <
      selected.tailSteps root.limit + 2 + (root.limit + 1) *
        (identity_actual_tuple_steps (identity_actual_node_steps root.limit height)
          root.limit (selected.tailSteps root.limit + 1) + 1)
    omega

end ActualSourceOrdinaryCurrentReduction

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- The ordinary recurrence includes the exact selected frame and its deferred bound. -/
private theorem identity_actual_source_selected_inner_work
    (limit _own : Nat) (point : IdentityActualSourcePoint bits) (height : Nat)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
    (caller : Caller (bits + 2)) (queries : Queries) (ownCache : Cached) (rowSeed : Seed)
    (children : List (Node × List Suspended)) :
    let parent := {point with height := height + 1}
    let inner : IdentityActualSourcePoint bits := {
      frame := .selected parent.frame parent.completed rest edge residual caller queries
        parent.height parent.count parent.bound,
      completed := [], caller := caller, before := ownCache, queries := queries,
      height := height, count := limit, bound := parent.bound + _own, mass := parent.mass, seed := rowSeed }
    IdentityActualSourceTask.work limit (.tuple inner children) <
      IdentityActualSourceTask.work limit (.rows height parent incoming bucket rest) := by
  dsimp only [IdentityActualSourceTask.work, IdentityActualSourcePoint.tailSteps, identity_actual_frame_steps]
  rw [Nat.succ_mul]
  omega

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- Forward source entry retains the exact original mathematical forecast. -/
private theorem identity_actual_source_forward_forecasts
    (recursiveDepth limit own : Nat) (point : IdentityActualSourcePoint bits) (count height : Nat)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended)) :
    ((IdentityActualSourceTask.goal recursiveDepth limit own
        (.tuple {point with count := count + 1} ((incoming, bucket) :: rest))).forecast =
      (IdentityActualSourceTask.goal recursiveDepth limit own
        (.child {point with count := count} incoming bucket rest)).forecast) ∧
    ((IdentityActualSourceTask.goal recursiveDepth limit own
        (.child {point with height := height + 1} incoming bucket rest)).forecast =
      (IdentityActualSourceTask.goal recursiveDepth limit own
        (.rows height {point with height := height + 1} incoming bucket rest)).forecast) := by
  exact ⟨rfl, rfl⟩

end ActualSourceOriginAndForwardCons
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualSelectedOwnScopePush
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain immutable actual scope entries and every deferred ancestor without future contracts. -/
private inductive IdentityActualFrameLedger
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (root : IdentityActualSourceRoot bits) (metadata : Metadata Unit) (uv : Nat) :
    IdentityActualCallbackFrame bits → Caller (bits + 2) → Cached → List (Node × List Suspended) → Prop where
  | captured (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (queries : Queries)
      (before rowOwn : Cached) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
      (residual : Option Constraint) (handle : Nat)
      (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
      (packet : Packet formulas solver inventory caller memos metadata before)
      (querySame : memos.query = queries)
      (ready : EnumerationDriver.Ready uv before.core)
      (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
      (incoming : EnumerationReferences.IncomingAvoid uv before.core)
      (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol, staged, residual), rowOwn)]) :
      IdentityActualFrameLedger formulas solver root metadata uv (.captured edge residual caller queries)
        caller rowOwn (staged.map (fun input => (input.1, input.2.1)))
  | selected (parent : IdentityActualCallbackFrame bits)
      (outerOriginal : Caller (bits + 2)) (outerBefore : Cached) (outerInputs : List (Node × List Suspended))
      (ancestors : IdentityActualFrameLedger formulas solver root metadata uv parent outerOriginal outerBefore outerInputs)
      (completed : List Fragment) (rest : List (Node × List Suspended))
      (incoming : Node) (bucket : List Suspended) (caller : Caller (bits + 2)) (queries : Queries)
      (before rowOwn : Cached) (edge : EdgeValue Symbol Constraint) (residual : Option Constraint)
      (height count bound mass : Nat) (seed : Seed) (inventory : Inventory) (memos : Memos)
      (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
      (packet : Packet formulas solver inventory caller memos metadata before)
      (querySame : memos.query = queries)
      (previous : TupleInputs formulas solver outerOriginal metadata outerBefore outerInputs completed caller queries before)
      (member : (incoming, bucket) ∈ outerInputs)
      (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket edge before =
        some [((edge.entry.key.symbol, staged, residual), rowOwn)])
      (snapshot : IdentityActualSourcePoint.Inputs formulas solver root outerOriginal metadata outerBefore outerInputs {
        frame := parent
        completed := completed
        caller := caller
        before := before
        queries := queries
        height := height
        count := count
        bound := bound
        mass := mass
        seed := seed } ((incoming, bucket) :: rest) (count + 1)) :
      IdentityActualFrameLedger formulas solver root metadata uv
        (.selected parent completed rest edge residual caller queries height count bound)
        caller rowOwn (staged.map (fun input => (input.1, input.2.1)))

/-- The prefix interpreter is exactly the existing actual ordinary scan. -/
private theorem identity_actual_source_row_prefix_run_eq
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat) (height : Nat) (point : IdentityActualSourcePoint bits)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended)) :
    identity_actual_source_row_prefix_run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      point incoming bucket rest (edgesOf incoming) =
    IdentityActualSourceTask.run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      (.rows height point incoming bucket rest) := by
  rfl

section SelectedOwnCurrentReduction
attribute [local irreducible] nodePlan tuplePlan fallbackPlan identity_actual_frame_plan
  identity_actual_frame_reserved IdentityActualSourceRoot.limit IdentityActualSourceRoot.own

/-- A real earlier row prefix and own preparation produce a new scope and retain all outer ledgers. -/
private theorem identity_actual_source_selected_own_current
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (root : IdentityActualSourceRoot bits) (outerOriginal : Caller (bits + 2))
    (outerBefore : Cached) (outerInputs : List (Node × List Suspended))
    (point : IdentityActualSourcePoint bits) (height : Nat)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (bucket : List Suspended) (rest : List (Node × List Suspended))
    (attempted remaining : List (EdgeValue Symbol Constraint)) (edge : EdgeValue Symbol Constraint)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (processed : List (SelectedEdge.Result (bits + 2))) (outputs : List (Output (bits + 2) Unit))
    (rowCaller : Caller (bits + 2)) (rowQueries : Queries)
    (origin : IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
      (.rows height {point with height := height + 1} (.node parentEntry rows depth free) bucket rest))
    (ancestors : IdentityActualFrameLedger formulas solver root metadata uv point.frame outerOriginal outerBefore outerInputs)
    (sourceRows : edgesOf (.node parentEntry rows depth free) = attempted ++ edge :: remaining)
    (past : identity_actual_source_row_prefix_run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
      {point with height := height + 1} (.node parentEntry rows depth free) bucket rest attempted =
        .complete processed outputs rowCaller rowQueries)
    (prefixInputs : IdentityActualSourcePoint.Inputs formulas solver root outerOriginal metadata outerBefore outerInputs
      {point with
        height := height + 1
        caller := rowCaller
        queries := rowQueries
        seed := identity_actual_source_row_boundary recursiveDepth root.limit root.own height
          {point with height := height + 1} attempted.length}
      ((.node parentEntry rows depth free, bucket) :: rest) (point.count + 1))
    (prefixFits : Fits (identity_actual_source_row_boundary recursiveDepth root.limit root.own height
      {point with height := height + 1} attempted.length).2 rowCaller.checked)
    (prefixKnown : Heap (fun guard => guard ∈ (identity_actual_source_row_boundary recursiveDepth root.limit root.own height
      {point with height := height + 1} attempted.length).1) rowCaller.checked.native.machine.heap)
    (admission : (IdentityActualSourceTask.goal recursiveDepth root.limit root.own
      (.child {point with height := height + 1} (.node parentEntry rows depth free) bucket rest)).reserved bits)
    (selectionMembers : ∀ selected ∈ edgesOf (.node parentEntry rows depth free), selected ∈ rows)
    (selectionLength : (edgesOf (.node parentEntry rows depth free)).length ≤ rows.length)
    (allowed : arityAllows edge.children.length bucket = true)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    let parent := {point with height := height + 1}
    let rowSeed := identity_actual_source_row_boundary recursiveDepth root.limit root.own height parent attempted.length
    let inputs := SourcePruningEnumerationEdgeInputs.children edge bucket point.before.core.counter tries
    let staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) :=
      inputs.map (fun input => (input.1, input.2,
        SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
    ∃ rowOwn : Cached,
      let inner := identity_actual_source_inner_point height root.limit root.own parent rest edge residual
        rowCaller rowQueries rowOwn rowSeed
      SourcePruningEnumerationCachedOwn.prepare rowCaller.checked.native.machine.heap bucket edge point.before =
        some [((edge.entry.key.symbol, staged, residual), rowOwn)] ∧
      IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
        (.tuple inner (staged.map (fun input => (input.1, input.2.1)))) ∧
      IdentityActualFrameLedger formulas solver root metadata uv inner.frame rowCaller rowOwn
        (staged.map (fun input => (input.1, input.2.1))) ∧
      IdentityActualSourceCurrent formulas solver root rowCaller metadata rowOwn
        (staged.map (fun input => (input.1, input.2.1))) recursiveDepth
        (.tuple inner (staged.map (fun input => (input.1, input.2.1)))) ∧
      TupleInputs formulas solver outerOriginal metadata outerBefore outerInputs point.completed rowCaller rowQueries point.before ∧
      TupleInputs formulas solver outerOriginal metadata outerBefore outerInputs point.completed rowCaller rowQueries rowOwn ∧
      SourcePruningEnumerationSharedChildVisitors.visitSelected
        (identity_actual_guarded_child checkEmpty edgesOf workFuel (.node parentEntry rows depth free))
        (SourcePruningEnumerationSharedEagerChildren.consumeSelected
          (identity_actual_parent_tail checkEmpty edgesOf workFuel
            (identity_actual_frame_callbacks graph checkEmpty edgesOf recursiveDepth workFuel metadata uv point.frame)
            point.completed rest) rowCaller rowQueries)
        bucket edge rowCaller point.before rowQueries =
          IdentityActualSourceTask.run graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
            (.tuple inner (staged.map (fun input => (input.1, input.2.1)))) ∧
      IdentityActualSourceTask.work root.limit (.tuple inner (staged.map (fun input => (input.1, input.2.1)))) <
        IdentityActualSourceTask.work root.limit (.rows height parent (.node parentEntry rows depth free) bucket rest) := by
  let parent := {point with height := height + 1}
  let rowSeed := identity_actual_source_row_boundary recursiveDepth root.limit root.own height parent attempted.length
  let inputs := SourcePruningEnumerationEdgeInputs.children edge bucket point.before.core.counter tries
  let staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) :=
    inputs.map (fun input => (input.1, input.2,
      SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
  have entrySnapshot := prefixInputs
  obtain ⟨shapes, kept, inventory, memos, packet, querySame, previous, mass, _counted, memberInputs, genuine⟩ := prefixInputs
  obtain ⟨available, closed, ranked, bucketBound, bounded, pending⟩ :=
    genuine (.node parentEntry rows depth free) bucket List.mem_cons_self
  have rowShapes := shapes.2 parentEntry rows depth free available
  have growth : ∀ retained current, Le current.2 (parent.tailPlan recursiveDepth root.limit root.own retained current).2 ∧
      current.1 ⊆ (parent.tailPlan recursiveDepth root.limit root.own retained current).1 := by
    intro retained current
    exact tuplePlan_ge (nodePlan root.limit root.own parent.height) (nodePlan_ge root.limit root.own parent.height)
      parent.count parent.bound retained (identity_actual_frame_plan recursiveDepth root.limit root.own parent.frame)
      (identity_actual_frame_plan_ge recursiveDepth root.limit root.own parent.frame) current
  obtain ⟨rowOwn, prepared, ownPacket, innerPrefix, ownFits, ownKnown, ownMass, counted, children,
      rowReserved, _rowIncluded, _rowRuntime⟩ :=
    identity_ordinary_row_prefix_reservation formulas solver inventory rowCaller memos metadata point.before
      root.caller.checked.native.machine.heap root.limit root.own height point.bound point.mass point.seed rowSeed
      (parent.tailPlan recursiveDepth root.limit root.own) (parent.tailReserved recursiveDepth root.limit root.own)
      parentEntry rows depth free edgesOf attempted remaining edge bucket tries residual
      packet prefixFits prefixKnown kept mass bucketBound available closed ranked bounded pending sourceRows
      selectionMembers selectionLength rowShapes allowed projected rfl admission growth
  have readback : staged.map (fun input => (input.1, input.2.1)) = inputs := by
    simp only [staged, List.map_map]
    exact List.map_id _
  have lower : ∀ child scs, (child, scs) ∈ staged.map (fun input => (input.1, input.2.1)) →
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free) := by
    intro child scs included
    rw [readback] at included
    exact (children child scs included).2.2.1
  have selected : edge ∈ rows := by
    apply selectionMembers edge
    rw [sourceRows]
    exact List.mem_append_right attempted List.mem_cons_self
  have outerAtOwn := (tuple_inputs_after_observed_own formulas solver outerOriginal metadata outerBefore
    outerInputs point.completed rowCaller rowQueries point.before bucket edge residual rowOwn staged previous prepared).1
  rw [querySame] at innerPrefix
  let inner := identity_actual_source_inner_point height root.limit root.own parent rest edge residual
    rowCaller rowQueries rowOwn rowSeed
  have newOrigin : IdentityActualSourceOrigin graph checkEmpty edgesOf recursiveDepth workFuel metadata uv root
      (.tuple inner (staged.map (fun input => (input.1, input.2.1)))) :=
    .selectedOwn point height parentEntry rows depth free bucket rest attempted remaining edge residual
      processed outputs rowCaller rowQueries rowOwn staged origin sourceRows selected past prepared lower
  have newLedger : IdentityActualFrameLedger formulas solver root metadata uv inner.frame rowCaller rowOwn
      (staged.map (fun input => (input.1, input.2.1))) :=
    .selected point.frame outerOriginal outerBefore outerInputs ancestors point.completed rest
      (.node parentEntry rows depth free) bucket rowCaller rowQueries point.before rowOwn edge residual
      parent.height parent.count parent.bound parent.mass rowSeed inventory memos staged packet querySame previous
      (memberInputs List.mem_cons_self) prepared entrySnapshot
  have innerInputs : IdentityActualSourcePoint.Inputs formulas solver root rowCaller metadata rowOwn
      (staged.map (fun input => (input.1, input.2.1))) inner (staged.map (fun input => (input.1, input.2.1))) root.limit := by
    refine ⟨shapes, kept, inventory, memos, ownPacket, querySame, innerPrefix, ownMass, ?_, ?_, ?_⟩
    · rw [readback]
      exact counted
    · intro pair included
      exact included
    · intro child scs included
      rw [readback] at included
      obtain ⟨childAvailable, childClosed, _strict, childRank, childBucket, childBounded, childPending⟩ := children child scs included
      exact ⟨childAvailable, childClosed, childRank, childBucket, childBounded, childPending⟩
  have innerReserved : (IdentityActualSourceTask.goal recursiveDepth root.limit root.own
      (.tuple inner (staged.map (fun input => (input.1, input.2.1))))).reserved bits := by
    change tupleReserved (nodePlan root.limit root.own height) (nodeReserved bits root.limit root.own height)
      root.limit (point.bound + root.own) point.mass
      (identity_actual_frame_plan recursiveDepth root.limit root.own
        (.selected point.frame point.completed rest edge residual rowCaller rowQueries
          parent.height parent.count parent.bound))
      (identity_actual_frame_reserved bits recursiveDepth root.limit root.own
        (.selected point.frame point.completed rest edge residual rowCaller rowQueries
          parent.height parent.count parent.bound)) rowSeed
    rw [identity_actual_frame_plan, identity_actual_frame_reserved]
    exact rowReserved
  have rowEquation := identity_selected_frame_generation graph checkEmpty edgesOf recursiveDepth workFuel metadata uv
    point.frame point.completed rest edge residual (.node parentEntry rows depth free) bucket rowCaller rowQueries
    point.before rowOwn parent.height parent.count parent.bound staged prepared lower
  refine ⟨rowOwn, prepared, newOrigin, newLedger, ⟨innerInputs, ownFits, ownKnown, innerReserved⟩,
    previous, outerAtOwn, ?_, ?_⟩
  · exact rowEquation
  · exact identity_actual_source_selected_inner_work root.limit root.own point height
      (.node parentEntry rows depth free) bucket rest edge residual rowCaller rowQueries rowOwn rowSeed
      (staged.map (fun input => (input.1, input.2.1)))

end SelectedOwnCurrentReduction
end ActualSelectedOwnScopePush
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualSourceOrderedRowForecast
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge iterate_add)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {bits : Nat}

/-- Each row seed follows the original fallback and ordered row schedule. -/
private noncomputable def IdentityActualSourcePoint.rowSeed
    (recursiveDepth limit own height : Nat) (point : IdentityActualSourcePoint bits) (index : Nat) : Seed :=
  let tail := point.tailPlan recursiveDepth limit own
  iterate (fun current => tuplePlan (nodePlan limit own height)
    limit (point.bound + own) point.mass tail current)
    (fallbackPlan point.bound point.mass tail point.seed) index

attribute [local irreducible] fallbackPlan nodePlan tuplePlan identity_actual_frame_plan

/-- A selected inner tuple ends at the exact next original row forecast. -/
private theorem identity_actual_source_row_inner_forecast
    (recursiveDepth limit own height index : Nat) (point : IdentityActualSourcePoint bits)
    (rest : List (Node × List Suspended)) (edge : EdgeValue Symbol Constraint)
    (residual : Option Constraint) (caller : Caller (bits + 2))
    (queries : Queries) (ownCache : Cached) (children : List (Node × List Suspended)) :
    let inner : IdentityActualSourcePoint bits := {
      frame := .selected point.frame point.completed rest edge residual caller queries
        point.height point.count point.bound
      completed := []
      caller := caller
      before := ownCache
      queries := queries
      height := height
      count := limit
      bound := point.bound + own
      mass := point.mass
      seed := point.rowSeed recursiveDepth limit own height index }
    (IdentityActualSourceTask.goal recursiveDepth limit own (.tuple inner children)).forecast =
      point.rowSeed recursiveDepth limit own height (index + 1) := by
  let tail := point.tailPlan recursiveDepth limit own
  let step := fun current => tuplePlan (nodePlan limit own height)
    limit (point.bound + own) point.mass tail current
  let first := fallbackPlan point.bound point.mass tail point.seed
  dsimp only [IdentityActualSourceTask.goal, IdentityReservationGoal.forecast]
  rw [identity_actual_frame_plan]
  change step (iterate step first index) = iterate step first (index + 1)
  exact (iterate_add step first index 1).symm

/-- Every actual earlier-row boundary fits the original complete row schedule. -/
private theorem identity_actual_source_row_prefix_forecast
    (recursiveDepth limit own height index : Nat) (point : IdentityActualSourcePoint bits)
    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (counted : index ≤ limit) :
    Le (point.rowSeed recursiveDepth limit own height index).2
      (IdentityActualSourceTask.goal recursiveDepth limit own (.rows height point incoming bucket rest)).forecast.2 ∧
    (point.rowSeed recursiveDepth limit own height index).1 ⊆
      (IdentityActualSourceTask.goal recursiveDepth limit own (.rows height point incoming bucket rest)).forecast.1 := by
  let tail := point.tailPlan recursiveDepth limit own
  let step := fun current => tuplePlan (nodePlan limit own height)
    limit (point.bound + own) point.mass tail current
  let first := fallbackPlan point.bound point.mass tail point.seed
  have tailGrowth : ∀ retained current, Le current.2 (tail retained current).2 ∧
      current.1 ⊆ (tail retained current).1 := by
    intro retained current
    exact tuplePlan_ge (nodePlan limit own point.height) (nodePlan_ge limit own point.height)
      point.count point.bound retained
      (identity_actual_frame_plan recursiveDepth limit own point.frame)
      (identity_actual_frame_plan_ge recursiveDepth limit own point.frame) current
  have stepGrowth : ∀ current, Le current.2 (step current).2 ∧ current.1 ⊆ (step current).1 := by
    intro current
    exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
      limit (point.bound + own) point.mass tail tailGrowth current
  have later := iterate_ge step stepGrowth (iterate step first index) (limit - index)
  rw [← iterate_add, Nat.add_sub_of_le counted] at later
  exact later

end ActualSourceOrderedRowForecast
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

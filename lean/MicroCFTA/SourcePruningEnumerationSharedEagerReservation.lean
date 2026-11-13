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
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def EagerResumeComplete
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
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (bound + extra) (bound + extra)
          (bound + extra) (bound + extra) (bound + extra) edgesOf)
        holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveDepth
        metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome

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
  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
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
  exact ⟨fuel, outcome, running, resources.mono included.1 included.2⟩
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
end ActualChildInputs

section ActualFallbackResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

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
      OutcomeResources formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
    rcases shape with rejected | ⟨fragment, singleton, afterSafe, fragmentBound, fragmentPending, fragmentAvoid⟩
    · obtain ⟨fuel, outcome, running, resources⟩ := no afterCaller savedQueries after outer waiting next final
        post query paddedFits paddedKnown reserved.2
      refine ⟨fuel, outcome, ?_, resources.post post⟩
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
      refine ⟨fuel, outcome, ?_, resources.post post⟩
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

private theorem eager_child_height_zero_complete
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own 0 formulas solver := by
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
  exact eager_fallback_resources seed bound ceiling continuation admitted formulas solver inventory caller memos metadata
    before checkEmpty edgesOf bucket incoming uv done stopped packet bounded pending
    (kept.available incoming capturedAvailable) closed fits known mass bucketBound reserved fallback
    (fun fragment reached saved after inputs bounded known mass accepted =>
      consumers.1 fragment reached saved after inputs (advance seed (bound + 1)) (ceiling + bound)
        bounded known mass accepted)
    (fun reached saved after outer waiting next final post query bounded known accepted =>
      consumers.2 reached saved after outer waiting next final post query (advance seed (bound + 1)) (ceiling + bound)
        bounded known accepted)
end ActualHeightBase

section ActualTupleConsumers
variable [DecidableEq (EdgeKey Symbol Constraint)]

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
  let visit : Nat → Visitor := fun fuel =>
    SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty fuel fuel fuel fuel fuel edgesOf
  exact tuple_nil_reserved_resources limit own height count bound ceiling continuation admitted growth seed formulas solver
    caller memos before uv visit done stopped fits known mass reserved (fun retained current bounded supported mass accepted =>
      consumers.1 [] caller memos.query before
        (tuple_inputs_nil formulas solver inventory caller memos metadata before packet)
        current retained bounded supported mass accepted)

private theorem eager_tuple_complete_of_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerTupleComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling inputs uv continuation admitted done stopped
        packet fits known kept mass length _genuine _shapes _selectionMembers _selectionLength reserved growth consumers
      cases inputs with
      | nil =>
          exact eager_tuple_nil_resources checkEmpty edgesOf limit own height 0 bound ceiling continuation admitted growth
            seed formulas solver inventory caller memos metadata before uv done stopped packet fits known mass reserved consumers
      | cons first rest => simp only [List.length_cons] at length; omega
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling inputs uv continuation admitted done stopped
        packet fits known kept mass length genuine shapes selectionMembers selectionLength reserved growth consumers
      cases inputs with
      | nil =>
          exact eager_tuple_nil_resources checkEmpty edgesOf limit own height (count + 1) bound ceiling continuation admitted growth
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
          have headConsumers : ChildConsumers formulas solver caller metadata before bucket uv tailPlan tailAdmitted yes no := by
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
              have tailConsumers : TupleConsumers formulas solver reached metadata after rest uv continuation admitted
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
              exact ⟨fuel, outcome, running, resources.mono included.1 included.2⟩
          obtain ⟨fuel, outcome, running, resources⟩ := child inventory caller memos metadata before seed bound ceiling bucket
            incoming uv tailPlan tailAdmitted yes no packet fits known available kept closed bounded pending mass bucketBound
            ranked shapes selectionMembers selectionLength reserved tailGrowth headConsumers
          refine ⟨fuel, outcome, ?_, resources⟩
          intro extra
          change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller before
            memos.query (yes (fuel + extra)) (no (fuel + extra)) = outcome
          exact running extra
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
          fun fuel fragments reached saved after =>
            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
              (.complete (.node edge.entry.key.symbol fragments) reached saved
                (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after))
        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
          fun fuel completed observation candidate =>
            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
              (.stopped completed observation candidate)
        have tupleConsumers : TupleConsumers formulas solver caller metadata middle inputs uv continuation admitted yes no := by
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
            have resources : OutcomeResources formulas solver reached current (finish uv outcome) := by
              refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
              intro output member
              cases member
            have enlarged := growth retained current
            exact ⟨0, outcome, fun _ => rfl, resources.mono enlarged.1 enlarged.2⟩
        have tuple := eager_tuple_complete_of_child (Typing := Typing) (bits := bits)
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
    · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
      intro output member
      cases member
end ActualSelectedResources

section ActualRowsConsumers
variable [DecidableEq (EdgeKey Symbol Constraint)]

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
  constructor
  · intro fragment reached saved after data current retained fitted supported mass accepted
    obtain ⟨next, final, post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩ := data
    exact consumers.1 fragment reached saved after
      ⟨next, final, earlier.trans post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩
      current retained fitted supported mass accepted
  · intro reached saved after outer waiting next final post query current retained fitted supported accepted
    exact consumers.2 reached saved after outer waiting next final (earlier.trans post) query
      current retained fitted supported accepted
end ActualRowsConsumers

section ActualRowsResources
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

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

private theorem eager_rows_complete_of_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerRowsComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped
        packet fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending
        alternatives length _selected _shapes _selectionMembers _selectionLength _reserved growth _consumers
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
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
          exact ⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
            supported, rfl, rfl, fun _ member => by cases member⟩
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_selected_resources
            checkEmpty edgesOf captured limit own height formulas solver child inventory caller memos metadata before seed
            bound ceiling scs uv continuation admitted done stopped packet fits known kept mass bucketBound
            parentEntry rows depth free available closed ranked edge (selected edge (by simp)) bounded pending
            shapes selectionMembers selectionLength firstReserved growth consumers
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
              have reachedConsumers := child_consumers_post formulas solver caller reached next final metadata before scs uv
                continuation admitted done stopped post consumers
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
                bound ceiling scs uv continuation admitted done stopped reachedPacket reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved growth reachedConsumers
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

private theorem eager_child_height_complete
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver := by
  induction height with
  | zero => exact eager_child_height_zero_complete checkEmpty edgesOf captured limit own formulas solver
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
            have rowsComplete := eager_rows_complete_of_child (Typing := Typing) (bits := bits)
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
        obtain ⟨fuel, outcome, running, resources⟩ := eager_fallback_resources seed bound ceiling continuation admitted
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
        exact ⟨fuel, outcome, running, resources.mono included.1 included.2⟩
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
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

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
              callback_eager_induction_resources holeKey keyMatches admits formulas solver next graph templates metadata uv
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
end ActualCapturedResources

section ActualCapturedRowsResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)

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
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_captured_resources
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
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
end ActualCapturedRowsResources

section ActualOpaqueResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

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
      callback_eager_induction_resources holeKey keyMatches admits formulas solver next graph templates metadata uv
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

end ActualOpaqueResources

section ActualPreparedResources
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate)

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
    obtain ⟨branchFuel, outcome, branchRun, certificate⟩ := eager_captured_rows_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
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
    obtain ⟨branchFuel, receipt, outcome, rawRun, receiptRun, certificate⟩ := eager_opaque_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
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
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, observed]
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
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, observed]
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
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, (phase extra).1]
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
    rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, currentPrefix]
    dsimp only
    rw [actual]

end ActualEagerExpansion

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
          simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] using running extra
      | some selected =>
          cases selected with
          | done =>
              obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
                checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata (some .done) seed
                packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] using running extra
          | stuck =>
              obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
                checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata (some .stuck) seed
                packet bounded known
              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
              intro extra
              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] using running extra
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

end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

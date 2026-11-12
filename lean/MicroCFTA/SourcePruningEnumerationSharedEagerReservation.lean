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

import MicroCFTA.MergedProjectionBound

/-!
# Complete group orders and canonical merged results

Reading the actual source rows gives a complete group order without an
external premise. Other complete orders produce the same full record in
a common valid cache. This isolates the effect of hash-table iteration.
-/
namespace MicroCFTA.MergedProjectionOrder
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- List each symbol at its first actual outgoing occurrence. -/
def observed (value : Value (Fin symbols) ConstraintKey) : List (Fin symbols) :=
  ((MergedRawLeafSource.rows value).map Prod.fst).eraseDups

/-- The actual outgoing records supply every required group symbol. -/
theorem observed_complete : MergedProjectionTargets.CompleteOrder (observed (symbols := symbols)) := by
  intro value symbol guard present
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨(symbol, guard), present, rfl⟩

/-- Complete group orders identify the same full merged record in a common later source cache. -/
theorem same_record (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (left right common : State (Fin symbols) ConstraintKey)
    (leftFacts : Facts left) (rightFacts : Facts right) (commonCoherent : Coherent common)
    (leftRepresented : Represents build (.leaf leaf) left value)
    (rightRepresented : Represents build (.leaf leaf) right value)
    (first second : List (Fin symbols))
    (firstComplete : MergedRawLeafSource.Complete first value)
    (secondComplete : MergedRawLeafSource.Complete second value)
    (firstGrowth : Grows (run (MergedRawLeafSource.worker first value) left).2 common)
    (secondGrowth : Grows (run (MergedRawLeafSource.worker second value) right).2 common) :
    (run (MergedRawLeafSource.worker first value) left).1 =
      (run (MergedRawLeafSource.worker second value) right).1 := by
  rw [MergedRawLeafSource.worker_eq_raw leaf value left leftFacts leftRepresented first firstComplete] at firstGrowth ⊢
  rw [MergedRawLeafSource.worker_eq_raw leaf value right rightFacts rightRepresented second secondComplete] at secondGrowth ⊢
  apply EqualityRawLeafIdentity.same_records _ _ left right common leftFacts.coherent.valid
    rightFacts.coherent.valid commonCoherent firstGrowth secondGrowth
  intro row
  apply and_congr _ Iff.rfl
  rw [MergedRawLeafSource.declarations_member leaf value left leftFacts leftRepresented first firstComplete row.1 row.2,
    MergedRawLeafSource.declarations_member leaf value right rightFacts rightRepresented second secondComplete row.1 row.2]

end MicroCFTA.MergedProjectionOrder

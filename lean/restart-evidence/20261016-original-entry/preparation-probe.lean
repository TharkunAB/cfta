import MicroCFTA.SourceEqualityOriginalAllocationPreparation
namespace MicroCFTA.OriginalPreparationProbe
open Cache Language SourceEqualityConstraintAllocation SourceEqualityOriginalAllocationHistory
open SourceEqualityOriginalAllocationPreparation
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Guard" => SourceSymbolicIndex.Constraint
#print axioms MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare
#print axioms MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_head_error
#print axioms MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_tail_error
#print axioms MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_cons_done
#print axioms MicroCFTA.SourceEqualityOriginalAllocationPreparation.Receipt.retained
#print axioms MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_complete
#print axioms MicroCFTA.SourceEqualityOriginalAllocationPreparation.Receipt.load
#check @MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare
#check @MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_head_error
#check @MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_tail_error
#check @MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_cons_done
#check @MicroCFTA.SourceEqualityOriginalAllocationPreparation.Receipt.retained
#check @MicroCFTA.SourceEqualityOriginalAllocationPreparation.prepare_complete
#check @MicroCFTA.SourceEqualityOriginalAllocationPreparation.Receipt.load

example (originals : List (Guard Formula)) (before : Cache.State Key) (valid : Cache.Valid before)
    (cached : ∀ original ∈ originals, SourceEqualityGuardReadback.Cached original.equalities) :
    ∃ values after, prepare originals before = (.ok values, after) ∧ History before after originals ∧
      Cache.Valid after ∧ Cache.Steps before after ∧ Cache.Extends before.table after.table ∧
      All₂ (Field after) originals values ∧
      ∀ original ∈ originals, ∃ value : SourceEqualityConjoinAllocation.Constraint Formula,
        SourceEqualityConstraintFieldLookup.load original after = .ok (some value) ∧
        SourceEqualityConjoinAllocation.readback value = original ∧ Ready after value.stored ∧
        SourceEqualityPhysicalPayload.read original.equalities = .ok value.stored.payload := by
  obtain ⟨values, after, receipt⟩ := prepare_complete originals before valid cached
  exact ⟨values, after, receipt.done, receipt.history, receipt.valid, receipt.steps, receipt.retained,
    receipt.fields, receipt.load⟩

example (original : Guard Formula) (before : Cache.State Key) (valid : Cache.Valid before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities) :
    ∃ value after, prepare [original, original] before = (.ok [value, value], after) ∧
      History before after [original, original] ∧ Cache.Extends before.table after.table := by
  have allCached : ∀ field ∈ [original, original], SourceEqualityGuardReadback.Cached field.equalities := by
    intro field member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact cached
  obtain ⟨values, after, receipt⟩ := prepare_complete [original, original] before valid allCached
  have done := receipt.done
  have history := receipt.history
  have retained := receipt.retained
  have fields := receipt.fields
  clear receipt
  cases fields with
  | cons first rest =>
      cases rest with
      | cons second last =>
          cases last
          have same := Option.some.inj (Except.ok.inj (first.2.1.symm.trans second.2.1))
          have sameValue := congrArg SourceEqualityConjoinAllocation.Constraint.stored same
          rcases sameValue with rfl
          exact ⟨_, after, done, history, retained⟩

example (original : Guard Formula) (rest : List (Guard Formula)) (before : Cache.State Key) (message : String)
    (failed : SourceEqualityPhysicalPayload.read original.equalities = .error message) :
    prepare (original :: rest) before = (.error message, before) := by
  apply prepare_head_error
  simp only [construct, failed]

def emptyGuard : Guard Unit := ⟨some [], .top⟩
def otherGuard : Guard Unit := ⟨some [[[0], [1]]], .top⟩
def malformedGuard : Guard Unit := ⟨some [[[], [0]]], .top⟩
def contradictionGuard : Guard Unit := ⟨none, .bottom⟩

def summarize (originals : List (Guard Unit)) (before : Cache.State Key) : Except String (List (Option Nat)) × Nat :=
  let result := prepare originals before
  (result.1.map (fun values => values.map Value.identity), result.2.next)

#eval summarize [emptyGuard, emptyGuard] (construct otherGuard.equalities Cache.emptyState).2
#eval summarize [emptyGuard, malformedGuard, otherGuard] Cache.emptyState
#eval summarize [contradictionGuard] (construct otherGuard.equalities Cache.emptyState).2

end MicroCFTA.OriginalPreparationProbe

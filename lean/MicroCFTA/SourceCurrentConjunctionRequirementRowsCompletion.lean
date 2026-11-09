import MicroCFTA.SourceCurrentConjunctionRequirementRowsEffects

/-!
# Successful forcing of resident shared row spines

Current equality readiness and resident raw tuples exclude equality faults.
The actual row traversal skips rejected tuples and retains the returned
equality state before it continues. Cached rows return without another fold.
No projection bound or future successful execution is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsCompletion
open InternedConstructorTemplates (EdgeValue)
open InternedNestedProvenance (Edges)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementRowsEffects (RawInputs SpineInputs)
variable {Symbol Formula : Type}
local notation "Row" => EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- A resident tuple completes its actual equality fold and retains current readiness. -/
theorem prepareTuple_success (tuple : List Row) (before : Storage)
    (ready : Ready before.requirements.physical)
    (resident : Edges before.requirements.physical.heap tuple) :
    ∃ row after, prepareTuple tuple before = .done row after ∧ Ready after.requirements.physical := by
  obtain ⟨result, done, valid, _, _, _, _, fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.requirements.physical.heap
      before.requirements.physical.equality ready.valid ready.fields resident
  have retained : Ready (prepareTuple tuple before).state.requirements.physical := by
    rw [prepareTuple_physical]
    exact ⟨ready.semantic, ready.costs, valid, fields⟩
  have completes : ∃ row after, prepareTuple tuple before = .done row after := by
    simp only [prepareTuple, done]
    split <;> exact ⟨_, _, rfl⟩
  obtain ⟨row, after, actual⟩ := completes
  exact ⟨row, after, actual, by simpa only [actual, Outcome.state] using retained⟩

private theorem pending_success (handle : Nat) (tuples : List (List Row)) (before : Storage)
    (ready : Ready before.requirements.physical) (raw : SpineInputs before)
    (found : lookupSpine handle before = some (.pending tuples)) :
    ∃ row after, nextRow handle before = .done row after := by
  induction tuples generalizing before with
  | nil => exact ⟨none, _, nextRow_nil handle before found⟩
  | cons tuple rest ih =>
      have resident := raw (.pending (tuple :: rest)) (List.mem_of_getElem? found)
        tuple List.mem_cons_self
      obtain ⟨row, after, prepared, nextReady⟩ := prepareTuple_success tuple before ready resident
      cases row with
      | some handles => exact ⟨_, _, nextRow_live handle tuple rest before after handles found prepared⟩
      | none =>
          have spines := prepareTuple_spines tuple before
          rw [prepared] at spines
          change after.spines = before.spines at spines
          have heapSame : after.requirements.physical.heap = before.requirements.physical.heap := by
            have physical := prepareTuple_physical tuple before
            rw [prepared] at physical
            have sameHeap := congrArg
              (fun state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula => state.heap) physical
            exact sameHeap
          have afterRaw : SpineInputs after := by
            intro spine member
            rw [spines] at member
            change RawInputs after.requirements.physical.heap spine
            rw [heapSame]
            exact raw spine member
          have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [spines]
            exact found
          have suffix : RawInputs after.requirements.physical.heap (.pending rest) := by
            intro next member
            exact afterRaw (.pending (tuple :: rest)) (List.mem_of_getElem? afterFound)
              next (List.mem_cons_of_mem _ member)
          have remaining : SpineInputs (updateSpine handle (.pending rest) after) := by
            intro spine member
            rcases List.mem_or_eq_of_mem_set member with old | same
            · exact afterRaw spine old
            · exact same.symm ▸ suffix
          have nextFound := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after afterFound
          obtain ⟨result, final, actual⟩ :=
            ih (updateSpine handle (.pending rest) after) nextReady remaining nextFound
          refine ⟨result, final, ?_⟩
          rw [nextRow_rejected handle tuple rest before after found prepared]
          exact actual

/-- Every present row spine succeeds from its current resident raw tuples and equality readiness. -/
theorem nextRow_success (handle : Nat) (before : Storage)
    (ready : Ready before.requirements.physical) (raw : SpineInputs before)
    (present : ∃ spine, lookupSpine handle before = some spine) :
    ∃ row after, nextRow handle before = .done row after := by
  obtain ⟨spine, found⟩ := present
  cases spine with
  | done row => exact ⟨row, before, nextRow_hit handle row before found⟩
  | pending tuples => exact pending_success handle tuples before ready raw found

end MicroCFTA.SourceCurrentConjunctionRequirementRowsCompletion

import MicroCFTA.SourceCurrentConjunctionRequirementRows
import MicroCFTA.InternedFreshOrdinaryProbeHeap

/-!
# Clean probes through actual shared row preparation

Tuple preparation changes only equality operations and private cells.
Row traversal performs preparation and private spine updates. Neither
operation forces a requirement or changes the value heap. The exact heap
identity therefore retains clean probes on successful and failed outcomes.
No readiness, residency, or future result premise is required here.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes
open InternedConstructorTemplates (EdgeValue)
open SourceCurrentConjunctionRequirementRows
variable {Symbol Formula : Type}
local notation "Row" => EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

private theorem pending_same_heap (handle : Nat) (tuples : List (List Row)) (before : Storage)
    (found : lookupSpine handle before = some (.pending tuples)) :
    (nextRow handle before).state.requirements.physical.heap = before.requirements.physical.heap := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      rfl
  | cons tuple rest ih =>
      have first : (prepareTuple tuple before).state.requirements.physical.heap =
          before.requirements.physical.heap := by rw [prepareTuple_physical]
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [prepared] at first
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          exact first
      | done row after =>
          rw [prepared] at first
          change after.requirements.physical.heap = before.requirements.physical.heap at first
          cases row with
          | some handles =>
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact first
          | none =>
              have retained := prepareTuple_spines tuple before
              rw [prepared] at retained
              change after.spines = before.spines at retained
              have present : lookupSpine handle after = some (.pending (tuple :: rest)) := by
                change after.spines[handle]? = some (.pending (tuple :: rest))
                rw [retained]
                exact found
              have nextFound := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after present
              rw [nextRow_rejected handle tuple rest before after found prepared]
              exact (ih (updateSpine handle (.pending rest) after) nextFound).trans first

/-- Every actual tuple preparation outcome retains the identical original value heap. -/
theorem prepareTuple_heap (tuple : List Row) (before : Storage) :
    (prepareTuple tuple before).state.requirements.physical.heap = before.requirements.physical.heap := by
  rw [prepareTuple_physical]

/-- Every actual row observation retains the identical original value heap. -/
theorem nextRow_heap (handle : Nat) (before : Storage) :
    (nextRow handle before).state.requirements.physical.heap = before.requirements.physical.heap := by
  cases found : lookupSpine handle before with
  | none =>
      rw [nextRow_missing handle before found]
      rfl
  | some spine =>
      cases spine with
      | done row =>
          rw [nextRow_hit handle row before found]
          rfl
      | pending tuples =>
          exact pending_same_heap handle tuples before found

/-- Actual tuple preparation retains probes at its identical returned value heap. -/
theorem prepareTuple_probes (tuple : List Row) (before : Storage)
    (probes : ProbeHeap before.requirements.physical.heap) :
    ProbeHeap (prepareTuple tuple before).state.requirements.physical.heap := by
  rw [prepareTuple_heap]
  exact probes

/-- Actual row forcing retains probes at its identical returned value heap on every outcome. -/
theorem nextRow_probes (handle : Nat) (before : Storage)
    (probes : ProbeHeap before.requirements.physical.heap) :
    ProbeHeap (nextRow handle before).state.requirements.physical.heap := by
  rw [nextRow_heap]
  exact probes

end MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes

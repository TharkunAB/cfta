import MicroCFTA.SourceCurrentConjunctionRequirementRows

/-!
# Actual cache publication for shared requirements

Every successful force stores its exact returned value at the same handle.
These laws inspect the actual execution. They do not force another cell or
row, and they do not assume that the final private heap is already cached.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementPublication
open InternedConstructorTemplates
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Rows" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- Every successful row observation caches its exact returned head at the same handle. -/
theorem nextRow_done (handle : Nat) (before after : Rows)
    (result : Option (List Nat × Nat))
    (actual : SourceCurrentConjunctionRequirementRows.nextRow handle before = .done result after) :
    SourceCurrentConjunctionRequirementRows.lookupSpine handle after = some (.done result) := by
  open SourceCurrentConjunctionRequirementRows in
  cases found : lookupSpine handle before with
  | none =>
      rw [nextRow_missing handle before found] at actual
      cases actual
  | some spine =>
      cases spine with
      | done cached =>
          rw [nextRow_hit handle cached before found] at actual
          cases actual
          exact found
      | pending tuples =>
          induction tuples generalizing before after result with
          | nil =>
              rw [nextRow_nil handle before found] at actual
              cases actual
              exact lookupSpine_update handle (.pending []) (.done none) before found
          | cons tuple rest ih =>
              have spines := prepareTuple_spines tuple before
              cases prepared : prepareTuple tuple before with
              | failed fault current =>
                  rw [nextRow_failed handle tuple rest before current fault found prepared] at actual
                  cases actual
              | done row current =>
                  rw [prepared] at spines
                  change current.spines = before.spines at spines
                  have retained : lookupSpine handle current = some (.pending (tuple :: rest)) := by
                    change current.spines[handle]? = some (.pending (tuple :: rest))
                    rw [spines]
                    exact found
                  cases row with
                  | none =>
                      rw [nextRow_rejected handle tuple rest before current found prepared] at actual
                      exact ih _ _ _ actual
                        (lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) current retained)
                  | some handles =>
                      rw [nextRow_live handle tuple rest before current handles found prepared] at actual
                      cases actual
                      have inside : handle < current.spines.length :=
                        (List.getElem?_eq_some_iff.mp retained).1
                      have appended : lookupSpine handle (allocateSpine (.pending rest) current).2 =
                          some (.pending (tuple :: rest)) := by
                        change (current.spines ++ [.pending rest])[handle]? = _
                        rw [List.getElem?_append_left inside]
                        exact retained
                      exact lookupSpine_update handle (.pending (tuple :: rest))
                        (.done (some (handles, (allocateSpine (.pending rest) current).1)))
                        (allocateSpine (.pending rest) current).2 appended

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem forceStep_complete (p h handle : Nat) (before after : Cells) (nodes : List Node)
    (actual : SourceCurrentConjunctionRequirementCells.forceStep p h handle before = .done (.complete nodes) after) :
    SourceCurrentConjunctionRequirementCells.lookup handle after = some (.done nodes) := by
  open SourceCurrentConjunctionRequirementCells in
  cases found : lookup handle before with
  | none => simp only [forceStep, found] at actual; cases actual
  | some cell =>
      cases cell with
      | done cached =>
          simp only [forceStep, found] at actual
          cases actual
          exact found
      | column original =>
          simp only [forceStep, found] at actual
          cases actual
          exact lookup_update handle (.column original)
            (.done (SourceCurrentConjunctionRequirements.canonical original)) before found
      | pending cursor =>
          cases observed : SourceCurrentConjunctionRequirementPull.step p h cursor before.physical with
          | failed fault physical =>
              simp only [forceStep, found, observed] at actual
              cases actual
          | done event physical =>
              cases event with
              | more cursor =>
                  simp only [forceStep, found, observed] at actual
                  cases actual
              | complete output =>
                  simp only [forceStep, found, observed] at actual
                  cases actual
                  exact lookup_update handle (.pending cursor) (.done nodes)
                    {before with physical := physical} found

/-- A successful finite requirement force caches the exact canonical result at its own handle. -/
theorem force_done (p h handle : Nat) (before after : Cells) (nodes : List Node)
    (actual : SourceCurrentConjunctionRequirementCells.force p h handle before = .done nodes after) :
    SourceCurrentConjunctionRequirementCells.lookup handle after = some (.done nodes) := by
  open SourceCurrentConjunctionRequirementCells in
  suffices ∀ weight (current : Cells), remaining handle current = weight →
      force p h handle current = .done nodes after → lookup handle after = some (.done nodes) by
    exact this _ before rfl actual
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured completed
      rw [force_step] at completed
      cases observed : forceStep p h handle current with
      | failed fault physical =>
          simp only [observed] at completed
          cases completed
      | done event physical =>
          cases event with
          | complete output =>
              simp only [observed] at completed
              cases completed
              exact forceStep_complete p h handle current after nodes observed
          | more cursor =>
              simp only [observed] at completed
              have decrease : remaining handle physical < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current physical cursor observed
              exact smaller _ decrease physical rfl completed

end MicroCFTA.SourceCurrentConjunctionRequirementPublication

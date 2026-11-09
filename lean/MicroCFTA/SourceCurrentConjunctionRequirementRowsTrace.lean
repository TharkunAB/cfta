import MicroCFTA.SourceCurrentConjunctionRequirementRows

/-!
# Actual source-order row preparation

Rejected prefixes retain each actual contradiction and its returned state.
The terminal observation retains the first live tuple, its exact allocated
row, and its fresh unforced suffix, or the exact first preparation fault.
Missing and cached handles have separate observations. The actual finite
worker derives this trace without readiness or semantic assumptions.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsTrace
open InternedConstructorTemplates (EdgeValue)
open SourceCurrentConjunctionRequirementRows
variable {Symbol Formula : Type}
local notation "Tuple" => List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Observation" => SourceCurrentConjunctionRequirementRows.Outcome Symbol Formula (Option (Handles × Nat))

/-- Rejection is an actual contradiction and retains the identical private cell list. -/
theorem prepareTuple_none {tuple : Tuple} {before after : Storage}
    (actual : prepareTuple tuple before = .done none after) :
    ∃ operations, SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality =
        (.ok (some .contradiction), operations) ∧
      after = {before with requirements := {before.requirements with
        physical := ⟨before.requirements.physical.heap, operations⟩}} := by
  cases folded : SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality with
  | mk answer operations =>
      cases answer with
      | error message =>
          simp only [prepareTuple, folded] at actual
          cases actual
      | ok result =>
          cases result with
          | none =>
              simp only [prepareTuple, folded] at actual
              cases actual
          | some result =>
              cases result with
              | contradiction =>
                  simp only [prepareTuple, folded, SourceEqualityConstraintAllocation.Value.payload,
                    SourceEqualityInheritedPayload.classes, Option.map_none] at actual
                  cases actual
                  exact ⟨operations, rfl, rfl⟩
              | live identity records =>
                  simp only [prepareTuple, folded, SourceEqualityConstraintAllocation.Value.payload,
                    SourceEqualityInheritedPayload.classes, Option.map_some] at actual
                  cases actual

/-- Live preparation allocates exactly the selected tuple's literal ordered descriptors. -/
theorem prepareTuple_some {tuple : Tuple} {before after : Storage} {handles : Handles}
    (actual : prepareTuple tuple before = .done (some handles) after) :
    ∃ operations result constraints,
      SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality =
          (.ok (some result), operations) ∧
      SourceEqualityInheritedPayload.classes result.payload = some constraints ∧
      let current : Cells := {before.requirements with
        physical := ⟨before.requirements.physical.heap, operations⟩}
      let allocated := allocateCells (descriptors tuple constraints) current
      handles = allocated.1 ∧ after = {before with requirements := allocated.2} := by
  cases folded : SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality with
  | mk answer operations =>
      cases answer with
      | error message =>
          simp only [prepareTuple, folded] at actual
          cases actual
      | ok result =>
          cases result with
          | none =>
              simp only [prepareTuple, folded] at actual
              cases actual
          | some result =>
              cases classes : SourceEqualityInheritedPayload.classes result.payload with
              | none =>
                  simp only [prepareTuple, folded, classes] at actual
                  cases actual
              | some constraints =>
                  simp only [prepareTuple, folded, classes] at actual
                  have parts := Outcome.done.inj actual
                  exact ⟨operations, result, constraints, rfl, classes,
                    (Option.some.inj parts.1).symm, parts.2.symm⟩

/-- A prefix records each actual rejected head before the same handle advances to its suffix. -/
inductive Rejected (handle : Nat) : List Tuple → Storage → List Tuple → Storage → Prop where
  | refl {tuples : List Tuple} {before : Storage} : Rejected handle tuples before tuples before
  | step {tuple : Tuple} {rest remaining : List Tuple} {before after final : Storage}
      (prepared : prepareTuple tuple before = .done none after)
      (tail : Rejected handle rest (updateSpine handle (.pending rest) after) remaining final) :
      Rejected handle (tuple :: rest) before remaining final

/-- The retained raw tuples form the exact suffix after the rejected original prefix. -/
theorem Rejected.prefix {handle : Nat} {original remaining : List Tuple} {before after : Storage}
    (actual : Rejected handle original before remaining after) :
    ∃ skipped, original = skipped ++ remaining := by
  induction actual with
  | refl => exact ⟨[], rfl⟩
  | @step tuple rest remaining before after final prepared tail ih =>
      obtain ⟨skipped, same⟩ := ih
      exact ⟨tuple :: skipped, congrArg (List.cons tuple) same⟩

/-- The first terminal head is exhausted, failed, or live with an exact unforced tail allocation. -/
inductive Finish (handle : Nat) : List Tuple → Storage → Observation → Prop where
  | exhausted {before : Storage} :
      Finish handle [] before (.done none (updateSpine handle (.done none) before))
  | failed {tuple : Tuple} {rest : List Tuple} {before after : Storage} {fault : Fault}
      (prepared : prepareTuple tuple before = .failed fault after) :
      Finish handle (tuple :: rest) before (.failed fault after)
  | live {tuple : Tuple} {rest : List Tuple} {before after : Storage} {handles : Handles}
      (prepared : prepareTuple tuple before = .done (some handles) after) :
      Finish handle (tuple :: rest) before
        (.done (some (handles, after.spines.length))
          (updateSpine handle (.done (some (handles, after.spines.length)))
            (allocateSpine (.pending rest) after).2))

/-- A row observation separates identity hits from actual source-order tuple preparation. -/
inductive Trace (handle : Nat) (before : Storage) : Observation → Prop where
  | missing (absent : lookupSpine handle before = none) : Trace handle before (.failed (.missing handle) before)
  | cached {row : Option (Handles × Nat)} (found : lookupSpine handle before = some (.done row)) :
      Trace handle before (.done row before)
  | pending {original remaining : List Tuple} {current : Storage} {outcome : Observation}
      (found : lookupSpine handle before = some (.pending original))
      (rejected : Rejected handle original before remaining current)
      (finished : Finish handle remaining current outcome) : Trace handle before outcome

private theorem pending_trace (handle : Nat) (tuples : List Tuple) (before : Storage)
    (found : lookupSpine handle before = some (.pending tuples)) :
    ∃ remaining current, Rejected handle tuples before remaining current ∧
      Finish handle remaining current (nextRow handle before) := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      exact ⟨[], before, .refl, .exhausted⟩
  | cons tuple rest ih =>
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          exact ⟨tuple :: rest, before, .refl, .failed prepared⟩
      | done row after =>
          cases row with
          | some handles =>
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact ⟨tuple :: rest, before, .refl, .live prepared⟩
          | none =>
              have retained := prepareTuple_spines tuple before
              rw [prepared] at retained
              change after.spines = before.spines at retained
              have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
                change after.spines[handle]? = some (.pending (tuple :: rest))
                rw [retained]
                exact found
              have nextFound := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after afterFound
              rw [nextRow_rejected handle tuple rest before after found prepared]
              obtain ⟨remaining, current, skipped, finished⟩ := ih
                (updateSpine handle (.pending rest) after) nextFound
              exact ⟨remaining, current, .step prepared skipped, finished⟩

/-- Every actual finite row observation derives its source-order trace and exact stopped state. -/
theorem nextRow_trace (handle : Nat) (before : Storage) : Trace handle before (nextRow handle before) := by
  cases found : lookupSpine handle before with
  | none =>
      rw [nextRow_missing handle before found]
      exact .missing found
  | some spine =>
      cases spine with
      | done row =>
          rw [nextRow_hit handle row before found]
          exact .cached found
      | pending tuples =>
          obtain ⟨remaining, current, rejected, finished⟩ := pending_trace handle tuples before found
          exact .pending found rejected finished

end MicroCFTA.SourceCurrentConjunctionRequirementRowsTrace

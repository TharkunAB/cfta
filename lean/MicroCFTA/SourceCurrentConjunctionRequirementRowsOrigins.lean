import MicroCFTA.SourceCurrentConjunctionRequirementRows

/-!
# Finite credits for actual shared row spines

Each allocated spine has one fixed natural-number credit. A pending raw
suffix fits within that credit. A cached live row points to a present tail
with a smaller credit. The actual allocator and row worker derive these
credits from the raw tuple lengths. This invariant does not assume a rank
for a future row. It does not select these heaps in the worklist.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsOrigins
open InternedConstructorTemplates
open SourceCurrentConjunctionRequirementRows
variable {Symbol Formula : Type}
local notation "Row" => EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "SpineState" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- Pending suffixes fit their own credit. Cached live tails have smaller credits. -/
def Bound (credits : List Nat) (credit : Nat) : Spine Symbol Formula → Prop
  | .pending tuples => tuples.length ≤ credit
  | .done none => True
  | .done (some (_, tail)) => ∃ next, credits[tail]? = some next ∧ next < credit

/-- Credits are aligned with all actual spine handles, including cached tails. -/
structure Credits (credits : List Nat) (state : SpineState) : Prop where
  length : credits.length = state.spines.length
  cells : ∀ handle cell, lookupSpine handle state = some cell →
    ∃ credit, credits[handle]? = some credit ∧ Bound credits credit cell

private theorem append_lookup {values : List Nat} (added : List Nat)
    {handle credit : Nat} (found : values[handle]? = some credit) :
    (values ++ added)[handle]? = some credit := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem append_bound (credits added : List Nat) (credit : Nat)
    (cell : Spine Symbol Formula) (bound : Bound credits credit cell) :
    Bound (credits ++ added) credit cell := by
  cases cell with
  | pending tuples => exact bound
  | done row =>
      cases row with
      | none => trivial
      | some row =>
          obtain ⟨next, found, smaller⟩ := bound
          exact ⟨next, append_lookup added found, smaller⟩

/-- The actual initial row heap has no handles and needs no credits. -/
theorem initial (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Credits [] (SourceCurrentConjunctionRequirementRows.initial before) := by
  refine ⟨rfl, ?_⟩
  intro handle cell found
  change ([] : List (Spine Symbol Formula))[handle]? = some cell at found
  simp only [List.getElem?_nil] at found
  cases found

/-- Requirement-cell or physical updates retain credits when the spine list is unchanged. -/
theorem same_spines {credits : List Nat} {before after : SpineState}
    (valid : Credits credits before) (same : after.spines = before.spines) :
    Credits credits after := by
  refine ⟨by rw [same]; exact valid.length, ?_⟩
  intro handle cell found
  apply valid.cells handle cell
  change after.spines[handle]? = some cell at found
  change before.spines[handle]? = some cell
  rw [same] at found
  exact found

private theorem update_credits {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) {handle credit : Nat}
    (own : credits[handle]? = some credit) (replacement : Spine Symbol Formula)
    (bound : Bound credits credit replacement) :
    Credits credits (updateSpine handle replacement before) := by
  have inside : handle < before.spines.length := by
    have bounded := (List.getElem?_eq_some_iff.mp own).1
    rw [valid.length] at bounded
    exact bounded
  refine ⟨by simpa only [updateSpine, List.length_set] using valid.length, ?_⟩
  intro index cell found
  change (before.spines.set handle replacement)[index]? = some cell at found
  by_cases same : handle = index
  · subst index
    rw [List.getElem?_set_self inside] at found
    cases found
    exact ⟨credit, own, bound⟩
  · rw [List.getElem?_set_ne same] at found
    exact valid.cells index cell found

/-- Actual pending allocation appends its literal raw length as the only new credit. -/
theorem allocate_pending {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) (tuples : List (List Row)) :
    Credits (credits ++ [tuples.length]) (allocateSpine (.pending tuples) before).2 := by
  refine ⟨by simpa only [allocateSpine, List.length_append, List.length_singleton]
    using congrArg (fun n => n + 1) valid.length, ?_⟩
  intro handle cell found
  by_cases inside : handle < before.spines.length
  · have original : lookupSpine handle before = some cell := by
      change (before.spines ++ [Spine.pending tuples])[handle]? = some cell at found
      rw [List.getElem?_append_left inside] at found
      exact found
    obtain ⟨credit, own, bound⟩ := valid.cells handle cell original
    exact ⟨credit, append_lookup _ own, append_bound _ _ _ _ bound⟩
  · have allocated : handle < before.spines.length + 1 := by
      have bounded := (List.getElem?_eq_some_iff.mp found).1
      simpa only [allocateSpine, List.length_append, List.length_singleton] using bounded
    have last : handle = before.spines.length := by omega
    subst handle
    have stored := lookupSpine_allocate (Spine.pending tuples) before
    have same : Spine.pending tuples = cell := Option.some.inj (stored.symm.trans found)
    cases same
    refine ⟨tuples.length, ?_, Nat.le_refl _⟩
    rw [← valid.length]
    simp

/-- Every actual tuple preparation outcome retains the same spine credits. -/
theorem prepareTuple_credits {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) (tuple : List Row) :
    Credits credits (prepareTuple tuple before).state :=
  same_spines valid (prepareTuple_spines tuple before)

private theorem pending_credits (tuples : List (List Row)) :
    ∀ (handle : Nat) (before : SpineState) (credits : List Nat),
      Credits credits before → lookupSpine handle before = some (.pending tuples) →
      ∃ added, Credits (credits ++ added) (nextRow handle before).state := by
  induction tuples with
  | nil =>
      intro handle before credits valid found
      obtain ⟨credit, own, _⟩ := valid.cells handle (.pending []) found
      refine ⟨[], ?_⟩
      rw [nextRow_nil handle before found]
      simpa only [List.append_nil, Outcome.state] using
        update_credits valid own (.done none) True.intro
  | cons tuple rest ih =>
      intro handle before credits valid found
      obtain ⟨credit, own, bound⟩ := valid.cells handle (.pending (tuple :: rest)) found
      change (tuple :: rest).length ≤ credit at bound
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          have kept := prepareTuple_credits valid tuple
          rw [prepared] at kept
          refine ⟨[], ?_⟩
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          simpa only [List.append_nil, Outcome.state] using kept
      | done result after =>
          have retained := prepareTuple_spines tuple before
          rw [prepared] at retained
          change after.spines = before.spines at retained
          have kept : Credits credits after := same_spines valid retained
          cases result with
          | none =>
              have shorter : Bound credits credit (Spine.pending rest) := by
                change rest.length ≤ credit
                simp only [List.length_cons] at bound
                omega
              have continued := update_credits kept own (.pending rest) shorter
              have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
                change after.spines[handle]? = some (.pending (tuple :: rest))
                rw [retained]
                exact found
              have nextFound := lookupSpine_update handle (.pending (tuple :: rest))
                (.pending rest) after afterFound
              obtain ⟨added, post⟩ := ih handle _ credits continued nextFound
              refine ⟨added, ?_⟩
              rw [nextRow_rejected handle tuple rest before after found prepared]
              exact post
          | some row =>
              have allocated := allocate_pending kept rest
              have tailCredit : (credits ++ [rest.length])[after.spines.length]? =
                  some rest.length := by
                rw [← kept.length]
                simp
              have smaller : rest.length < credit := by
                simp only [List.length_cons] at bound
                omega
              have published := update_credits allocated (append_lookup [rest.length] own)
                (Spine.done (some (row, after.spines.length)))
                (show Bound (credits ++ [rest.length]) credit
                  (Spine.done (some (row, after.spines.length))) from
                  ⟨rest.length, tailCredit, smaller⟩)
              refine ⟨[rest.length], ?_⟩
              rw [nextRow_live handle tuple rest before after row found prepared]
              exact published

/-- Every actual row outcome derives appended credits and preserves all earlier credits. -/
theorem nextRow_credits (handle : Nat) {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) :
    ∃ added, Credits (credits ++ added) (nextRow handle before).state := by
  cases found : lookupSpine handle before with
  | none =>
      refine ⟨[], ?_⟩
      rw [nextRow_missing handle before found]
      simpa only [List.append_nil, Outcome.state] using valid
  | some cell =>
      cases cell with
      | pending tuples => exact pending_credits tuples handle before credits valid found
      | done row =>
          refine ⟨[], ?_⟩
          rw [nextRow_hit handle row before found]
          simpa only [List.append_nil, Outcome.state] using valid

/-- A cached live tail has a valid handle and a strictly smaller fixed credit. -/
theorem cached_tail {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) (handle tail : Nat) (row : Handles)
    (found : lookupSpine handle before = some (.done (some (row, tail)))) :
    ∃ own next, credits[handle]? = some own ∧ credits[tail]? = some next ∧
      next < own ∧ tail < before.spines.length := by
  obtain ⟨own, ownFound, bound⟩ := valid.cells handle _ found
  obtain ⟨next, nextFound, smaller⟩ := bound
  refine ⟨own, next, ownFound, nextFound, smaller, ?_⟩
  have inside := (List.getElem?_eq_some_iff.mp nextFound).1
  rw [valid.length] at inside
  exact inside

end MicroCFTA.SourceCurrentConjunctionRequirementRowsOrigins

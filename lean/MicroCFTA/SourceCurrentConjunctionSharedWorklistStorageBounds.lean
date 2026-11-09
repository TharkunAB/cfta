import MicroCFTA.SourceCurrentConjunctionSharedWorklistRun

/-!
# Original-budget bounds for shared row storage

A pending spine carries its remaining tuple count and an extra charge.
A cached live row carries one unit. A cached end carries the extra charge.
Actual row forcing never increases this mass. Repeated cached reads add
nothing. A positive sample pays for its new spine from its consumed budget.

The original run therefore bounds cached live rows and pending raw tuples
by its original budget. It bounds the spine count by twice that budget.
These laws include failed outcomes. They do not bound requirement-cell
descriptors, projection work or the native heap.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistStorageBounds
open InternedConstructorTemplates (Value EdgeValue EdgeKey)
open SourceCurrentConjunctionRequirementRows (Spine lookupSpine updateSpine allocateSpine prepareTuple nextRow
  nextRow_nil nextRow_failed nextRow_rejected nextRow_live nextRow_missing nextRow_hit
  prepareTuple_spines lookupSpine_update)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistRun (Run)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

/-- A pending tuple or cached live row uses one unit; extra charges account for spine storage. -/
def spineWeight (extra : Nat) : Spine Symbol Formula → Nat
  | .pending tuples => tuples.length + extra
  | .done none => extra
  | .done (some _) => 1

/-- Sum the actual pending and cached spine charges. -/
def mass (extra : Nat) (before : Storage) : Nat :=
  (before.spines.map (spineWeight extra)).sum

private def pendingLength : Spine Symbol Formula → Nat
  | .pending tuples => tuples.length
  | .done _ => 0

private def liveCount : Spine Symbol Formula → Nat
  | .done (some _) => 1
  | _ => 0

/-- Count every raw tuple retained in the actual pending spine cells. -/
def pendingTuples (before : Storage) : Nat := (before.spines.map pendingLength).sum

/-- Count the actual cached live row heads, without recounting cached observations. -/
def liveRows (before : Storage) : Nat := (before.spines.map liveCount).sum

private theorem mass_stats (before : Storage) :
    mass 0 before = liveRows before + pendingTuples before ∧
    mass 1 before = before.spines.length + pendingTuples before := by
  suffices ∀ spines : List (Spine Symbol Formula),
      (spines.map (spineWeight 0)).sum = (spines.map liveCount).sum + (spines.map pendingLength).sum ∧
      (spines.map (spineWeight 1)).sum = spines.length + (spines.map pendingLength).sum by
    exact this before.spines
  intro spines
  induction spines with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
      obtain ⟨zero, one⟩ := ih
      cases first with
      | pending tuples =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, spineWeight, pendingLength, liveCount]
          constructor <;> omega
      | done row =>
          cases row <;>
            simp only [List.map_cons, List.sum_cons, List.length_cons, spineWeight, pendingLength, liveCount] <;>
            constructor <;> omega

private theorem set_mass (extra : Nat) (spines : List (Spine Symbol Formula)) (handle : Nat)
    (original replacement : Spine Symbol Formula) (found : spines[handle]? = some original) :
    ((spines.set handle replacement).map (spineWeight extra)).sum + spineWeight extra original =
      (spines.map (spineWeight extra)).sum + spineWeight extra replacement := by
  induction spines generalizing handle with
  | nil => cases handle <;> cases found
  | cons first rest ih =>
      cases handle with
      | zero =>
          have same : spineWeight extra first = spineWeight extra original :=
            congrArg (spineWeight extra) (Option.some.inj found)
          change spineWeight extra replacement + (rest.map (spineWeight extra)).sum + spineWeight extra original =
            spineWeight extra first + (rest.map (spineWeight extra)).sum + spineWeight extra replacement
          omega
      | succ handle =>
          change rest[handle]? = some original at found
          have same := ih handle found
          change spineWeight extra first + ((rest.set handle replacement).map (spineWeight extra)).sum +
              spineWeight extra original =
            spineWeight extra first + (rest.map (spineWeight extra)).sum + spineWeight extra replacement
          omega

private theorem update_mass (extra handle : Nat) (original replacement : Spine Symbol Formula)
    (before : Storage) (found : lookupSpine handle before = some original) :
    mass extra (updateSpine handle replacement before) + spineWeight extra original =
      mass extra before + spineWeight extra replacement :=
  set_mass extra before.spines handle original replacement found

private theorem allocate_mass (extra : Nat) (cell : Spine Symbol Formula) (before : Storage) :
    mass extra (allocateSpine cell before).2 = mass extra before + spineWeight extra cell := by
  change ((before.spines ++ [cell]).map (spineWeight extra)).sum =
    (before.spines.map (spineWeight extra)).sum + spineWeight extra cell
  rw [List.map_append, List.sum_append] <;> rfl

private theorem pending_mass (extra handle : Nat) (tuples : List (List Row)) :
    ∀ before : Storage, lookupSpine handle before = some (.pending tuples) →
      mass extra (nextRow handle before).state ≤ mass extra before := by
  induction tuples with
  | nil =>
      intro before found
      have changed := update_mass extra handle (.pending []) (.done none) before found
      simp only [spineWeight, List.length_nil] at changed
      rw [nextRow_nil handle before found]
      change mass extra (updateSpine handle (.done none) before) ≤ mass extra before
      omega
  | cons tuple rest ih =>
      intro before found
      have kept := prepareTuple_spines tuple before
      cases prepared : prepareTuple tuple before with
      | failed fault current =>
          rw [prepared] at kept
          change current.spines = before.spines at kept
          rw [nextRow_failed handle tuple rest before current fault found prepared]
          change mass extra current ≤ mass extra before
          have sameMass : mass extra current = mass extra before := by unfold mass; rw [kept]
          exact Nat.le_of_eq sameMass
      | done row current =>
          rw [prepared] at kept
          change current.spines = before.spines at kept
          have sameMass : mass extra current = mass extra before := by unfold mass; rw [kept]
          have currentFound : lookupSpine handle current = some (.pending (tuple :: rest)) := by
            change current.spines[handle]? = some (.pending (tuple :: rest))
            rw [kept]
            exact found
          cases row with
          | none =>
              have changed := update_mass extra handle (.pending (tuple :: rest)) (.pending rest) current currentFound
              simp only [spineWeight, List.length_cons] at changed
              have smaller : mass extra (updateSpine handle (.pending rest) current) ≤ mass extra current := by omega
              have continued := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) current currentFound
              have tail := ih (updateSpine handle (.pending rest) current) continued
              rw [nextRow_rejected handle tuple rest before current found prepared]
              exact Nat.le_trans tail (Nat.le_trans smaller (Nat.le_of_eq sameMass))
          | some handles =>
              let added := allocateSpine (.pending rest) current
              have inside : handle < current.spines.length := (List.getElem?_eq_some_iff.mp currentFound).1
              have appended : lookupSpine handle added.2 = some (.pending (tuple :: rest)) := by
                change (current.spines ++ [.pending rest])[handle]? = some (.pending (tuple :: rest))
                rw [List.getElem?_append_left inside]
                exact currentFound
              have changed := update_mass extra handle (.pending (tuple :: rest))
                (.done (some (handles, added.1))) added.2 appended
              have allocated : mass extra added.2 = mass extra current + spineWeight extra (.pending rest) :=
                allocate_mass extra (.pending rest) current
              simp only [spineWeight, List.length_cons] at changed allocated
              rw [nextRow_live handle tuple rest before current handles found prepared]
              change mass extra (updateSpine handle (.done (some (handles, added.1))) added.2) ≤ mass extra before
              omega

/-- Every actual row outcome retains or decreases pending and cached mass, including faults and cache hits. -/
theorem nextRow_mass (extra handle : Nat) (before : Storage) :
    mass extra (nextRow handle before).state ≤ mass extra before := by
  cases found : lookupSpine handle before with
  | none => rw [nextRow_missing handle before found]; exact Nat.le_refl _
  | some cell =>
      cases cell with
      | done row => rw [nextRow_hit handle row before found]; exact Nat.le_refl _
      | pending tuples => exact pending_mass extra handle tuples before found

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem visit_mass_budget (extra h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) :
    mass extra (visit h nodes rest before).state.storage + (extra + 1) * (visit h nodes rest before).state.budget ≤
      mass extra before.storage + (extra + 1) * before.budget := by
  cases empty : nodes.any isEmpty with
  | true => rw [visit_empty h nodes rest before empty]; exact Nat.le_refl _
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
          before.budget (queryTable before.table) nodes with
      | true => rw [visit_skip h nodes rest before empty skipped]; exact Nat.le_refl _
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact Nat.le_refl _
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  change mass extra before.storage + (extra + 1) * 0 ≤
                    mass extra before.storage + (extra + 1) * before.budget
                  omega
              | fit tuples =>
                  cases tuples with
                  | nil => rw [visit_zero h nodes rest before physical empty skipped sampled]; exact Nat.le_refl _
                  | cons tuple tuples =>
                      have fits := SourceCurrentConjunctionTuplePullTotal.sample_bounded h before.budget nodes
                        before.storage.requirements.physical physical (.fit (tuple :: tuples)) sampled
                      change (tuple :: tuples).length ≤ before.budget at fits
                      have cap : tuples.length + 1 ≤ before.budget := by simpa only [List.length_cons] using fits
                      have scaled : extra ≤ extra * (tuples.length + 1) := by
                        simpa only [Nat.mul_one] using
                          Nat.mul_le_mul_left extra (Nat.succ_le_succ (Nat.zero_le tuples.length))
                      have charge : tuples.length + 1 + extra ≤ (extra + 1) * (tuples.length + 1) := by
                        rw [Nat.add_mul, Nat.one_mul]
                        omega
                      have accounting : (extra + 1) * before.budget =
                          (extra + 1) * (before.budget - (tuples.length + 1)) + (extra + 1) * (tuples.length + 1) := by
                        rw [← Nat.mul_add, Nat.sub_add_cancel cap]
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      change mass extra (allocateSpine (.pending (tuple :: tuples)) (withPhysical before physical).storage).2 +
                          (extra + 1) * (before.budget - (tuples.length + 1)) ≤
                        mass extra before.storage + (extra + 1) * before.budget
                      rw [allocate_mass]
                      change mass extra before.storage + ((tuple :: tuples).length + extra) +
                          (extra + 1) * (before.budget - (tuples.length + 1)) ≤
                        mass extra before.storage + (extra + 1) * before.budget
                      simp only [List.length_cons]
                      omega

/-- Every literal step pays for row storage from its current budget on success and failure. -/
theorem step_mass_budget (extra p h : Nat) (before : WorkState) :
    mass extra (step p h before).state.storage + (extra + 1) * (step p h before).state.budget ≤
      mass extra before.storage + (extra + 1) * before.budget := by
  cases pending : before.pending with
  | nil => rw [step_nil p h before pending]; exact Nat.le_refl _
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_mass_budget extra h nodes rest before
      | requirements handles =>
          cases handles with
          | nil => rw [step_requirements_nil p h before rest pending]; exact Nat.le_refl _
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact Nat.le_refl _
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_mass_budget extra h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
      | rows handle =>
          have first := nextRow_mass extra handle before.storage
          cases advanced : nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              apply Nat.add_le_add_right _ ((extra + 1) * before.budget)
              simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state, Outcome.state] using first
          | done row storage =>
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  apply Nat.add_le_add_right _ ((extra + 1) * before.budget)
                  simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state, Outcome.state] using first
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  apply Nat.add_le_add_right _ ((extra + 1) * before.budget)
                  simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state, Outcome.state] using first

private theorem run_mass_budget (extra : Nat) {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : Run p h before outcome) :
    mass extra outcome.state.storage + (extra + 1) * outcome.state.budget ≤
      mass extra before.storage + (extra + 1) * before.budget := by
  induction actual with
  | @failed before after fault advanced =>
      simpa only [advanced, Outcome.state] using step_mass_budget extra p h before
  | @drained before after advanced =>
      simpa only [advanced, Outcome.state] using step_mass_budget extra p h before
  | @more before middle outcome advanced tail ih =>
      have first : mass extra middle.storage + (extra + 1) * middle.budget ≤
          mass extra before.storage + (extra + 1) * before.budget := by
        simpa only [advanced, Outcome.state] using step_mass_budget extra p h before
      exact Nat.le_trans ih first

/-- Original empty private storage derives the conserved budget bound at every actual exploration outcome. -/
theorem explore_mass_budget (extra p h budget : Nat) (start : Node) (before : Physical) :
    let after := SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before
    mass extra after.state.storage + (extra + 1) * after.state.budget ≤ (extra + 1) * budget := by
  have kept := run_mass_budget extra (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
  simpa only [SourceCurrentConjunctionSharedWorklistStep.initial,
    SourceCurrentConjunctionRequirementRows.initial, mass, List.map_nil, List.sum_nil, Nat.zero_add] using kept

/-- The actual original run stores at most twice its budget in spines and at most its budget in live or pending tuples. -/
theorem explore_storage_bound (p h budget : Nat) (start : Node) (before : Physical) :
    let after := (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state
    after.storage.spines.length ≤ 2 * budget ∧
      liveRows after.storage + pendingTuples after.storage + after.budget ≤ budget := by
  let after := (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state
  change after.storage.spines.length ≤ 2 * budget ∧
    liveRows after.storage + pendingTuples after.storage + after.budget ≤ budget
  have counted : mass 1 after.storage + 2 * after.budget ≤ 2 * budget :=
    explore_mass_budget 1 p h budget start before
  have worked : mass 0 after.storage + after.budget ≤ budget := by
    simpa only [after, Nat.zero_add, Nat.one_mul] using explore_mass_budget 0 p h budget start before
  have stats := mass_stats after.storage
  rw [stats.1] at worked
  rw [stats.2] at counted
  exact ⟨by omega, worked⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistStorageBounds

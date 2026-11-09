import MicroCFTA.SourceCurrentConjunctionRequirementCellsValues
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual

/-!
# Closed values in shared requirement cells

Every stored column, completed value, collected prefix, and pending forest
is closed. Actual cell forcing preserves these facts on all outcomes.
Successful forcing also returns closed nodes. Singleton projection closure
follows from its actual source graph and the current resident closed forest.
The proof does not require a future successful projection or callback.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRowsWorker (Physical Job)
open SourceCurrentConjunctionRequirementCells
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "CellState" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- Each cell retains closed literal values and closed forests in its pending jobs. -/
def CellClosed : Cell Symbol Formula → Prop
  | .column nodes | .done nodes => ClosedValues nodes
  | .pending cursor => ClosedValues cursor.collected ∧ ∀ job ∈ cursor.pending, ClosedValues job.1

/-- Every actual stored cell has closed current operands. -/
def Invariant (before : CellState) : Prop :=
  ∀ handle cell, lookup handle before = some cell → CellClosed cell

/-- A suspended event retains closed operands and a completed event supplies closed nodes. -/
def EventClosed : Event Symbol Formula → Prop
  | .more cursor => CellClosed (.pending cursor)
  | .complete nodes => ClosedValues nodes

/-- Literal canonicalization retains only original closed values or Empty. -/
theorem canonical_closed (nodes : List Node) (closed : ClosedValues nodes) :
    ClosedValues (SourceCurrentConjunctionRequirements.canonical nodes) := by
  unfold SourceCurrentConjunctionRequirements.canonical
  split
  · intro value member
    cases List.mem_singleton.mp member
    rfl
  · intro value member
    obtain ⟨entry, present, same⟩ := List.mem_map.mp member
    cases same
    have found := SourceEqualityNeededMap.lookup_of_mem entry.1
      (SourceCurrentConjunctionMap.fromList SourceCurrentConjunctionRequirements.key nodes) entry.2
      (SourceCurrentConjunctionMap.fromList_ascending _ _) present
    exact closed entry.2
      (SourceCurrentConjunctionMap.fromList_origin _ nodes entry.1 entry.2 found).1

/-- The empty private cell heap has no closed-value obligation. -/
theorem initial_closed (before : Physical Symbol Formula) : Invariant (initial before) := by
  intro handle cell found
  cases handle <;> cases found

/-- Appending a closed descriptor preserves every earlier closed cell. -/
theorem allocate_closed (cell : Cell Symbol Formula) (before : CellState) (closed : Invariant before)
    (own : CellClosed cell) : Invariant (allocate cell before).2 := by
  intro handle next found
  have member : next ∈ before.cells ++ [cell] := List.mem_of_getElem? found
  rcases List.mem_append.mp member with old | new
  · obtain ⟨index, present⟩ := List.mem_iff_getElem?.mp old
    exact closed index next present
  · have same : next = cell := List.mem_singleton.mp new
    exact same.symm ▸ own

private theorem update_closed (target : Nat) (original replacement : Cell Symbol Formula)
    (before : CellState) (found : lookup target before = some original)
    (closed : Invariant before) (own : CellClosed replacement) :
    Invariant (update target replacement before) := by
  intro handle cell present
  by_cases same : handle = target
  · subst handle
    have inserted := lookup_update target original replacement before found
    have equal : replacement = cell := Option.some.inj (inserted.symm.trans present)
    exact equal ▸ own
  · have retained : lookup handle (update target replacement before) = lookup handle before :=
      List.getElem?_set_ne (Ne.symm same)
    exact closed handle cell (retained.symm.trans present)

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection_closed (p h : Nat) (job : Job Symbol Formula)
    (before after : Physical Symbol Formula) (value : Node) (ready : Ready before)
    (available : Values before.heap job.1) (closed : ClosedValues job.1)
    (actual : SourceCurrentConjunctionRequirementPull.projection p h job before = .done value after) :
    value.free = [] := by
  have singleton : SourceCurrentConjunctionRowsWorker.projections p h [job] before = .done [value] after := by
    rw [← SourceCurrentConjunctionRequirementPull.projection_singleton, actual]
    rfl
  have graph := (SourceCurrentConjunctionRowsWorkerActual.projections_graph singleton).1
  rcases job with ⟨forest, path⟩
  cases graph with
  | cons first rest =>
      cases rest
      obtain ⟨result, heap, completed, _, _, _, resultClosed⟩ :=
        SourceEqualityProjectionComplete.forest_complete (path.map Int.ofNat) forest before.heap
          ready.semantic available closed
      have same := (SourceEqualityProjectionAPI.forest_unique completed first).1
      exact same ▸ resultClosed

/-- Actual one-step forcing preserves closed cells and supplies closed successful events. -/
theorem forceStep_closed (p h handle : Nat) (before : CellState) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before) (closed : Invariant before) :
    Invariant (forceStep p h handle before).state ∧
      match forceStep p h handle before with
      | .done event _ => EventClosed event
      | .failed _ _ => True := by
  cases found : lookup handle before with
  | none =>
      simp only [forceStep, found, Outcome.state]
      exact ⟨closed, trivial⟩
  | some cell =>
      cases cell with
      | done nodes =>
          simp only [forceStep, found, Outcome.state]
          exact ⟨closed, closed handle _ found⟩
      | column nodes =>
          simp only [forceStep, found, Outcome.state]
          have result := canonical_closed nodes (closed handle _ found)
          exact ⟨update_closed handle _ _ before found closed result, result⟩
      | pending cursor =>
          rcases cursor with ⟨jobs, collected⟩
          have own := closed handle (.pending ⟨jobs, collected⟩) found
          have present := values handle (.pending ⟨jobs, collected⟩) found
          cases jobs with
          | nil =>
              simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, Outcome.state]
              have result := canonical_closed collected own.1
              exact ⟨update_closed handle _ _ before found closed result, result⟩
          | cons job rest =>
              cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before.physical with
              | failed fault after =>
                  simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                    SourceCurrentConjunctionRowsWorker.Outcome.bind, Outcome.state]
                  exact ⟨closed, trivial⟩
              | done value after =>
                  have projected := projection_closed p h job before.physical after value ready
                    (present.2 job List.mem_cons_self) (own.2 job List.mem_cons_self) actual
                  cases empty : SourceCurrentConjunctionRequirements.isEmpty value with
                  | true =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, empty, ite_true, Outcome.state]
                      have result : ClosedValues [(.empty : Node)] := by
                        intro node member
                        cases List.mem_singleton.mp member
                        rfl
                      exact ⟨update_closed handle _ _ {before with physical := after} found closed result, result⟩
                  | false =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, empty, Bool.false_eq_true,
                        ite_false, Outcome.state]
                      have current : CellClosed (.pending ⟨rest, collected ++ [value]⟩) := by
                        constructor
                        · intro node member
                          rcases List.mem_append.mp member with old | new
                          · exact own.1 node old
                          · cases List.mem_singleton.mp new
                            exact projected
                        · intro later member
                          exact own.2 later (List.mem_cons_of_mem _ member)
                      exact ⟨update_closed handle _ _ {before with physical := after} found closed current, current⟩

/-- Finite forcing preserves closed cells on faults and returns closed canonical nodes on success. -/
theorem force_closed (p h handle : Nat) (before : CellState) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before) (closed : Invariant before) :
    Invariant (force p h handle before).state ∧
      match force p h handle before with
      | .done nodes _ => ClosedValues nodes
      | .failed _ _ => True := by
  suffices ∀ weight (current : CellState), remaining handle current = weight →
      Ready current.physical → SourceCurrentConjunctionRequirementCellsValues.Invariant current → Invariant current →
      Invariant (force p h handle current).state ∧
        match force p h handle current with
        | .done nodes _ => ClosedValues nodes
        | .failed _ _ => True by
    exact this _ before rfl ready values closed
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured ready values closed
      rw [force_step]
      have first := SourceCurrentConjunctionRequirementCellsValues.forceStep_values p h handle current ready values
      have second := forceStep_closed p h handle current ready values closed
      cases actual : forceStep p h handle current with
      | failed fault after => simpa only [actual, Outcome.state] using second
      | done event after =>
          have reached : SourceCurrentConjunctionRowsAllocation.Effects current.physical after.physical ∧
              SourceCurrentConjunctionRequirementCellsValues.Invariant after ∧
              SourceCurrentConjunctionRequirementCellsValues.EventValues after.physical.heap event := by
            simpa only [actual, Outcome.state] using first
          have currentClosed : Invariant after ∧ EventClosed event := by
            simpa only [actual, Outcome.state] using second
          cases event with
          | complete nodes => exact currentClosed
          | more cursor =>
              have decrease : remaining handle after < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current after cursor actual
              exact smaller _ decrease after rfl reached.1.ready reached.2.1 currentClosed.1

end MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed

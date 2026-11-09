import MicroCFTA.SourceCurrentConjunctionRequirementCellsEffects

/-!
# Available values in shared requirement cells

Columns and completed cells contain resident nodes. A pending cell also
retains its collected prefix and its current job operands. Actual forcing
preserves these facts on every outcome. Successful forcing supplies resident
canonical nodes. The laws require no closedness or future successful read.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsValues
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Physical Job)
open SourceCurrentConjunctionRequirementCells
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "CellState" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- Each cell retains exactly the operands and values that it currently stores. -/
def CellValues (heap : InternedConstructorTemplates.State Symbol Guard) : Cell Symbol Formula → Prop
  | .column nodes | .done nodes => Values heap nodes
  | .pending cursor => Values heap cursor.collected ∧ ∀ job ∈ cursor.pending, Values heap job.1

/-- Every actual stored handle has its current resident values. -/
def Invariant (before : CellState) : Prop :=
  ∀ handle cell, lookup handle before = some cell → CellValues before.physical.heap cell

/-- Suspended results retain their prefix and jobs; completed results retain their nodes. -/
def EventValues (heap : InternedConstructorTemplates.State Symbol Guard) : Event Symbol Formula → Prop
  | .more cursor => CellValues heap (.pending cursor)
  | .complete nodes => Values heap nodes

/-- Literal canonicalization returns only inserted nodes or the available Empty constructor. -/
theorem canonical_available (nodes : List Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (available : Values heap nodes) : Values heap (SourceCurrentConjunctionRequirements.canonical nodes) := by
  unfold SourceCurrentConjunctionRequirements.canonical
  split
  · intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact empty_available heap
  · intro value member
    obtain ⟨entry, present, same⟩ := List.mem_map.mp member
    cases same
    have found := SourceEqualityNeededMap.lookup_of_mem entry.1
      (SourceCurrentConjunctionMap.fromList SourceCurrentConjunctionRequirements.key nodes) entry.2
      (SourceCurrentConjunctionMap.fromList_ascending _ _) present
    exact available entry.2
      (SourceCurrentConjunctionMap.fromList_origin _ nodes entry.1 entry.2 found).1

/-- The empty private cell heap has no stored value obligation. -/
theorem initial_values (before : Physical Symbol Formula) : Invariant (initial before) := by
  intro handle cell found
  cases handle <;> cases found

/-- Appending a current resident descriptor preserves the complete cell invariant. -/
theorem allocate_values (cell : Cell Symbol Formula) (before : CellState) (inputs : Invariant before)
    (own : CellValues before.physical.heap cell) : Invariant (allocate cell before).2 := by
  intro handle next found
  have member : next ∈ before.cells ++ [cell] := List.mem_of_getElem? found
  rcases List.mem_append.mp member with old | new
  · obtain ⟨index, present⟩ := List.mem_iff_getElem?.mp old
    exact inputs index next present
  · have same : next = cell := List.mem_singleton.mp new
    exact same.symm ▸ own

private theorem weak_inputs (before : CellState) (inputs : Invariant before) :
    SourceCurrentConjunctionRequirementCellsEffects.Inputs before := by
  intro handle cell found
  cases cell with
  | column nodes | done nodes => trivial
  | pending cursor => exact (inputs handle _ found).2

private theorem values_grows {before after : InternedConstructorTemplates.State Symbol Guard}
    (kept : SourceEqualityRequiredCache.Keeps before after) (nodes : List Node)
    (available : Values before nodes) : Values after nodes := by
  intro value member
  exact kept.available value (available value member)

private theorem cellValues_grows {before after : InternedConstructorTemplates.State Symbol Guard}
    (kept : SourceEqualityRequiredCache.Keeps before after) (cell : Cell Symbol Formula)
    (available : CellValues before cell) : CellValues after cell := by
  cases cell with
  | column nodes | done nodes => exact values_grows kept nodes available
  | pending cursor =>
      exact ⟨values_grows kept cursor.collected available.1,
        fun job member => values_grows kept job.1 (available.2 job member)⟩

private theorem invariant_grows (before : CellState) (after : Physical Symbol Formula)
    (kept : SourceEqualityRequiredCache.Keeps before.physical.heap after.heap) (inputs : Invariant before) :
    Invariant {before with physical := after} := by
  intro handle cell found
  exact cellValues_grows kept cell (inputs handle cell found)

private theorem update_values (target : Nat) (original replacement : Cell Symbol Formula)
    (before : CellState) (after : Physical Symbol Formula) (found : lookup target before = some original)
    (inputs : Invariant before) (kept : SourceEqualityRequiredCache.Keeps before.physical.heap after.heap)
    (own : CellValues after.heap replacement) : Invariant (update target replacement {before with physical := after}) := by
  intro handle cell present
  by_cases same : handle = target
  · subst handle
    have inserted := lookup_update target original replacement {before with physical := after} found
    have equal : replacement = cell := Option.some.inj (inserted.symm.trans present)
    exact equal ▸ own
  · have retained : lookup handle (update target replacement {before with physical := after}) =
        lookup handle before := List.getElem?_set_ne (Ne.symm same)
    exact cellValues_grows kept cell (inputs handle cell (retained.symm.trans present))

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection_available (p h : Nat) (job : Job Symbol Formula)
    (before after : Physical Symbol Formula) (value : Node) (ready : Ready before)
    (available : Values before.heap job.1)
    (actual : SourceCurrentConjunctionRequirementPull.projection p h job before =
      .done value after) : Available after.heap value := by
  rcases job with ⟨forest, path⟩
  cases read : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
  | done output heap =>
      have graph := SourceEqualityProjectionWorkerSound.forest_graph p h (path.map Int.ofNat)
        forest before.heap output heap read
      have present := (SourceEqualityProjectionCosts.forest_effects graph ready.semantic ready.costs available).2.2.2
      simp only [SourceCurrentConjunctionRequirementPull.projection, SourceCurrentConjunctionRowsWorker.projections,
        read, SourceCurrentConjunctionRowsWorker.Outcome.bind, List.headD_cons] at actual
      have parts := SourceCurrentConjunctionRowsWorker.Outcome.done.inj actual
      have sameHeap : heap = after.heap := congrArg (fun state : Physical Symbol Formula => state.heap) parts.2
      rw [← parts.1, ← sameHeap]
      exact present
  | pending key heap | unresolved name heap | exhausted limit heap =>
      simp only [SourceCurrentConjunctionRequirementPull.projection, SourceCurrentConjunctionRowsWorker.projections,
        read, SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
      cases actual

/-- Every step preserves all stored values and derives the available values of its actual successful result. -/
theorem forceStep_values (p h handle : Nat) (before : CellState)
    (ready : Ready before.physical) (inputs : Invariant before) :
    Effects before.physical (forceStep p h handle before).state.physical ∧
      Invariant (forceStep p h handle before).state ∧
      match forceStep p h handle before with
      | .done event after => EventValues after.physical.heap event
      | .failed _ _ => True := by
  have first := SourceCurrentConjunctionRequirementCellsEffects.forceStep_effects p h handle before ready
    (weak_inputs before inputs)
  refine ⟨first.1, ?_⟩
  cases found : lookup handle before with
  | none =>
      simp only [forceStep, found, Outcome.state]
      exact ⟨inputs, trivial⟩
  | some cell =>
      cases cell with
      | done nodes =>
          simp only [forceStep, found, Outcome.state]
          exact ⟨inputs, inputs handle _ found⟩
      | column nodes =>
          simp only [forceStep, found, Outcome.state]
          have kept := Effects.refl before.physical ready
          have result := canonical_available nodes before.physical.heap (inputs handle _ found)
          exact ⟨update_values handle _ _ before before.physical found inputs kept.keeps result, result⟩
      | pending cursor =>
          rcases cursor with ⟨jobs, collected⟩
          have own := inputs handle (.pending ⟨jobs, collected⟩) found
          cases jobs with
          | nil =>
              simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, Outcome.state]
              have kept := Effects.refl before.physical ready
              have result := canonical_available collected before.physical.heap own.1
              exact ⟨update_values handle _ _ before before.physical found inputs kept.keeps result, result⟩
          | cons job rest =>
              have projected := SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job
                before.physical ready (own.2 job List.mem_cons_self)
              cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before.physical with
              | failed fault after =>
                  have kept : Effects before.physical after := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using projected
                  simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                    SourceCurrentConjunctionRowsWorker.Outcome.bind, Outcome.state]
                  exact ⟨invariant_grows before after kept.keeps inputs, trivial⟩
              | done value after =>
                  have kept : Effects before.physical after := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using projected
                  have present := projection_available p h job before.physical after value ready
                    (own.2 job List.mem_cons_self) actual
                  cases empty : SourceCurrentConjunctionRequirements.isEmpty value with
                  | true =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, empty, ite_true, Outcome.state]
                      have result : Values after.heap [(.empty : Node)] := by
                        intro node member
                        cases List.mem_singleton.mp member
                        exact empty_available after.heap
                      exact ⟨update_values handle _ _ before after found inputs kept.keeps result, result⟩
                  | false =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, empty, Bool.false_eq_true,
                        ite_false, Outcome.state]
                      have current : CellValues after.heap (.pending ⟨rest, collected ++ [value]⟩) := by
                        constructor
                        · intro node member
                          rcases List.mem_append.mp member with old | new
                          · exact kept.keeps.available node (own.1 node old)
                          · cases List.mem_singleton.mp new
                            exact present
                        · intro later member node included
                          exact kept.keeps.available node (own.2 later (List.mem_cons_of_mem _ member) node included)
                      exact ⟨update_values handle _ _ before after found inputs kept.keeps current, current⟩

/-- Complete finite forcing retains all stored values on faults and returns resident nodes on success. -/
theorem force_values (p h handle : Nat) (before : CellState)
    (ready : Ready before.physical) (inputs : Invariant before) :
    Effects before.physical (force p h handle before).state.physical ∧ Invariant (force p h handle before).state ∧
      match force p h handle before with
      | .done nodes after => Values after.physical.heap nodes
      | .failed _ _ => True := by
  suffices ∀ weight (current : CellState), remaining handle current = weight →
      Ready current.physical → Invariant current →
      Effects current.physical (force p h handle current).state.physical ∧ Invariant (force p h handle current).state ∧
        match force p h handle current with
        | .done nodes after => Values after.physical.heap nodes
        | .failed _ _ => True by
    exact this _ before rfl ready inputs
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured ready inputs
      rw [force_step]
      have first := forceStep_values p h handle current ready inputs
      cases actual : forceStep p h handle current with
      | failed fault after => simpa only [actual, Outcome.state] using first
      | done event after =>
          have kept : Effects current.physical after.physical ∧ Invariant after ∧ EventValues after.physical.heap event := by
            simpa only [actual, Outcome.state] using first
          cases event with
          | complete nodes => exact kept
          | more cursor =>
              have decrease : remaining handle after < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current after cursor actual
              obtain ⟨last, rest⟩ := smaller _ decrease after rfl kept.1.ready kept.2.1
              exact ⟨kept.1.trans last, rest⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsValues

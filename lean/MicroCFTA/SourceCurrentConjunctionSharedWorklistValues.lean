import MicroCFTA.SourceCurrentConjunctionSharedWorklistRun
import MicroCFTA.SourceCurrentConjunctionRequirementRowsValues
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalEffects

/-!
# Physical readiness throughout actual shared work

The current invariant covers stored cell values, raw tuples, pending
conjunctions, and table queries. Sampling, row preparation, and cell forcing
derive the facts at their actual returned states. The finite execution graph
then preserves the invariant through successful and failed outcomes.
No closedness or future successful computation is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistValues
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorklistStep
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula

/-- Every current operand has its resident source value and physical read invariants. -/
structure Invariant (before : WorkState) : Prop where
  ready : Ready before.storage.requirements.physical
  cells : SourceCurrentConjunctionRequirementCellsValues.Invariant before.storage.requirements
  raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs before.storage
  pending : ∀ nodes, Task.nodes nodes ∈ before.pending → Values before.storage.requirements.physical.heap nodes
  table : ∀ entry ∈ before.table, Values before.storage.requirements.physical.heap entry.nodes

private theorem values_grows {before after : InternedConstructorTemplates.State Symbol Guard}
    (kept : SourceEqualityRequiredCache.Keeps before after) (nodes : List Node) (available : Values before nodes) :
    Values after nodes := by
  intro node member
  exact kept.available node (available node member)

private theorem storage_values (before : WorkState) (storage : Storage) (values : Invariant before)
    (effects : Effects before.storage.requirements.physical storage.requirements.physical)
    (cells : SourceCurrentConjunctionRequirementCellsValues.Invariant storage.requirements)
    (raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs storage) :
    Invariant {before with storage := storage} :=
  ⟨effects.ready, cells, raw,
    fun nodes member => values_grows effects.keeps nodes (values.pending nodes member),
    fun entry member => values_grows effects.keeps entry.nodes (values.table entry member)⟩

private theorem physical_values (before : WorkState) (physical : Physical) (values : Invariant before)
    (effects : Effects before.storage.requirements.physical physical) : Invariant (withPhysical before physical) :=
  storage_values before (withPhysical before physical).storage values effects
    (SourceCurrentConjunctionRequirementRowsValues.cells_grows before.storage.requirements physical effects.keeps values.cells)
    (SourceCurrentConjunctionRequirementRowsValues.spines_grows before.storage
      (withPhysical before physical).storage effects.keeps rfl values.raw)

private theorem allocate_raw (tuples : List (List Row)) (storage : Storage)
    (raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs storage)
    (resident : ∀ tuple ∈ tuples, Edges storage.requirements.physical.heap tuple) :
    SourceCurrentConjunctionRequirementRowsEffects.SpineInputs
      (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending tuples) storage).2 := by
  intro spine member
  rcases List.mem_append.mp member with old | new
  · exact raw spine old
  · have same : spine = .pending tuples := List.mem_singleton.mp new
    cases same
    exact resident

/-- Empty private heaps and the available starting query derive the initial value invariant. -/
theorem initial_values (budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    Invariant (SourceCurrentConjunctionSharedWorklistStep.initial budget start before) := by
  refine ⟨ready, SourceCurrentConjunctionRequirementCellsValues.initial_values before, ?_, ?_, ?_⟩
  · intro spine member
    cases member
  · intro nodes member
    have same : nodes = [start] := Task.nodes.inj (List.mem_singleton.mp member)
    subst nodes
    intro node included
    cases List.mem_singleton.mp included
    exact available
  · intro entry member
    cases member

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A literal visit preserves physical effects and every current operand on all outcomes. -/
theorem visit_values (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (values : Invariant {before with pending := .nodes nodes :: rest}) :
    Effects before.storage.requirements.physical (visit h nodes rest before).state.storage.requirements.physical ∧
      Invariant (visit h nodes rest before).state := by
  have tail : ∀ query, Task.nodes query ∈ rest → Values before.storage.requirements.physical.heap query :=
    fun query member => values.pending query (List.mem_cons_of_mem _ member)
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact ⟨Effects.refl _ values.ready, ⟨values.ready, values.cells, values.raw, tail, values.table⟩⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact ⟨Effects.refl _ values.ready, ⟨values.ready, values.cells, values.raw, tail, values.table⟩⟩
      | false =>
          have first := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h before.budget nodes
            before.storage.requirements.physical values.ready (values.pending nodes List.mem_cons_self)
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              have kept : Effects before.storage.requirements.physical physical := by
                simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.1
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact ⟨kept, physical_values {before with pending := .nodes nodes :: rest} physical values kept⟩
          | done result physical =>
              have kept : Effects before.storage.requirements.physical physical := by
                simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first.1
              have current := physical_values {before with pending := .nodes nodes :: rest} physical values kept
              have remaining : ∀ query, Task.nodes query ∈ rest → Values physical.heap query :=
                fun query member => values_grows kept.keeps query (tail query member)
              have queryValues : Values physical.heap nodes :=
                values_grows kept.keeps nodes (values.pending nodes List.mem_cons_self)
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact ⟨kept, ⟨current.ready, current.cells, current.raw, remaining, current.table⟩⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      refine ⟨kept, ⟨current.ready, current.cells, current.raw, remaining, ?_⟩⟩
                      intro entry member
                      rcases List.mem_cons.mp member with same | member
                      · cases same
                        exact queryValues
                      · exact current.table entry member
                  | cons tuple tuples =>
                      have resident := first.2 (.fit (tuple :: tuples)) physical sampled
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      refine ⟨kept, ⟨current.ready, current.cells, allocate_raw (tuple :: tuples) _ current.raw resident, ?_, ?_⟩⟩
                      · intro query member
                        rcases List.mem_cons.mp member with impossible | member
                        · cases impossible
                        · exact remaining query member
                      · intro entry member
                        rcases List.mem_cons.mp member with same | member
                        · cases same
                          exact queryValues
                        · exact current.table entry member

/-- Every actual shared transition retains full physical effects and all resident work operands. -/
theorem step_values (p h : Nat) (before : WorkState) (values : Invariant before) :
    Effects before.storage.requirements.physical (step p h before).state.storage.requirements.physical ∧
      Invariant (step p h before).state := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact ⟨Effects.refl _ values.ready, values⟩
  | cons task rest =>
      have tail : ∀ nodes, Task.nodes nodes ∈ rest → Values before.storage.requirements.physical.heap nodes := by
        intro nodes member
        apply values.pending nodes
        rw [pending]
        exact List.mem_cons_of_mem _ member
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          apply visit_values
          rw [← pending]
          exact values
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact ⟨Effects.refl _ values.ready, ⟨values.ready, values.cells, values.raw, tail, values.table⟩⟩
          | cons handle handles =>
              have first := SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                before.storage.requirements values.ready values.cells
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  have kept : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using (And.intro first.1 first.2.1)
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact ⟨kept.1, storage_values before _ values kept.1 kept.2
                    (SourceCurrentConjunctionRequirementRowsValues.spines_grows before.storage _ kept.1.keeps rfl values.raw)⟩
              | done nodes cells =>
                  have kept : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧ Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using first
                  have current := storage_values before {before.storage with requirements := cells} values kept.1 kept.2.1
                    (SourceCurrentConjunctionRequirementRowsValues.spines_grows before.storage _ kept.1.keeps rfl values.raw)
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  have next : Invariant
                      {{before with storage := {before.storage with requirements := cells}} with
                        pending := .nodes nodes :: .requirements handles :: rest} := by
                    refine ⟨current.ready, current.cells, current.raw, ?_, current.table⟩
                    intro query member
                    rcases List.mem_cons.mp member with same | member
                    · have equal : query = nodes := Task.nodes.inj same
                      subst query
                      exact kept.2.2
                    · rcases List.mem_cons.mp member with impossible | member
                      · cases impossible
                      · exact values_grows kept.1.keeps query (tail query member)
                  have last := visit_values h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} next
                  exact ⟨kept.1.trans last.1, last.2⟩
      | rows handle =>
          have first := SourceCurrentConjunctionRequirementRowsValues.nextRow_values handle before.storage
            values.ready values.cells values.raw
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              have kept : Effects before.storage.requirements.physical storage.requirements.physical ∧
                  SourceCurrentConjunctionRequirementCellsValues.Invariant storage.requirements ∧
                  SourceCurrentConjunctionRequirementRowsEffects.SpineInputs storage := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact ⟨kept.1, storage_values before storage values kept.1 kept.2.1 kept.2.2⟩
          | done row storage =>
              have kept : Effects before.storage.requirements.physical storage.requirements.physical ∧
                  SourceCurrentConjunctionRequirementCellsValues.Invariant storage.requirements ∧
                  SourceCurrentConjunctionRequirementRowsEffects.SpineInputs storage := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
              have current := storage_values before storage values kept.1 kept.2.1 kept.2.2
              have remaining : ∀ nodes, Task.nodes nodes ∈ rest → Values storage.requirements.physical.heap nodes :=
                fun nodes member => values_grows kept.1.keeps nodes (tail nodes member)
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact ⟨kept.1, ⟨current.ready, current.cells, current.raw, remaining, current.table⟩⟩
              | some row =>
                  rcases row with ⟨handles, tailHandle⟩
                  rw [step_rows_live p h handle tailHandle before rest handles storage pending advanced]
                  refine ⟨kept.1, ⟨current.ready, current.cells, current.raw, ?_, current.table⟩⟩
                  intro nodes member
                  rcases List.mem_cons.mp member with impossible | member
                  · cases impossible
                  · rcases List.mem_cons.mp member with impossible | member
                    · cases impossible
                    · exact remaining nodes member

/-- The actual finite run graph composes reached invariants without an eager replay. -/
theorem run_values {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome) (values : Invariant before) :
    Effects before.storage.requirements.physical outcome.state.storage.requirements.physical ∧ Invariant outcome.state := by
  revert values
  induction actual with
  | @failed before after fault advanced =>
      intro values
      simpa only [advanced, Outcome.state] using step_values p h before values
  | @drained before after advanced =>
      intro values
      simpa only [advanced, Outcome.state] using step_values p h before values
  | @more before middle outcome advanced tail ih =>
      intro values
      have first : Effects before.storage.requirements.physical middle.storage.requirements.physical ∧ Invariant middle := by
        simpa only [advanced, Outcome.state] using step_values p h before values
      obtain ⟨last, final⟩ := ih first.2
      exact ⟨first.1.trans last, final⟩

/-- Original initialization derives all finite shared-iterator effects and operand invariants on every outcome. -/
theorem explore_values (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    Effects before (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state.storage.requirements.physical ∧
      Invariant (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state :=
  run_values (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (initial_values budget start before ready available)

end MicroCFTA.SourceCurrentConjunctionSharedWorklistValues

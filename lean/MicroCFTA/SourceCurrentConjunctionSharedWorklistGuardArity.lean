import MicroCFTA.SourceCurrentConjunctionSharedWorklistValues
import MicroCFTA.SourceCurrentConjunctionRequirementCellsGuardArity
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes
import MicroCFTA.SourceCurrentConjunctionDemandAnnotations

/-!
# Causal guards and arity through every shared exploration outcome

One private induction carries a current heap predicate through actual sample,
force and row steps. The public laws supply both concrete capabilities from
proved lower operations. No public future heap or successful run is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistGuardArity
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistValues (Invariant)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Each actual visit retains the heap predicate through skips, sampling, and every returned status. -/
private theorem visit_heap (property : Heap → Prop)
    (sampleKeeps : ∀ h budget (nodes : List Node) (before : Physical), Ready before →
      Values before.heap nodes → property before.heap →
      property (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap)
    (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (ready : Ready before.storage.requirements.physical)
    (known : property before.storage.requirements.physical.heap)
    (available : Values before.storage.requirements.physical.heap nodes) :
    property (visit h nodes rest before).state.storage.requirements.physical.heap := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact known
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact known
      | false =>
          have first := sampleKeeps h before.budget nodes
            before.storage.requirements.physical ready available known
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state,
                SourceCurrentConjunctionSharedWorklistStep.Outcome.state, withPhysical] using first
          | done result physical =>
              have clean : property physical.heap := by
                simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact clean
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      exact clean
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      exact clean

/-- Every shared transition preserves the heap predicate at its exact successful or failed endpoint. -/
private theorem step_heap (property : Heap → Prop)
    (sampleKeeps : ∀ h budget (nodes : List Node) (before : Physical), Ready before →
      Values before.heap nodes → property before.heap →
      property (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap)
    (forceKeeps : ∀ p h handle (before : SourceCurrentConjunctionRequirementCells.State Symbol Formula),
      Ready before.physical → SourceCurrentConjunctionRequirementCellsValues.Invariant before →
      property before.physical.heap →
      property (SourceCurrentConjunctionRequirementCells.force p h handle before).state.physical.heap)
    (p h : Nat) (before : WorkState) (values : Invariant before)
    (known : property before.storage.requirements.physical.heap) :
    property (step p h before).state.storage.requirements.physical.heap := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact known
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          apply visit_heap property sampleKeeps h nodes rest before values.ready known
          exact values.pending nodes (by rw [pending]; exact List.mem_cons_self)
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact known
          | cons handle handles =>
              have first := forceKeeps p h handle
                before.storage.requirements values.ready values.cells known
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state,
                    SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using first
              | done nodes cells =>
                  have clean : property cells.physical.heap := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using first
                  have own := SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                    before.storage.requirements values.ready values.cells
                  have current : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧ Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using own
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_heap property sampleKeeps h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                    current.1.ready clean current.2.2
      | rows handle =>
          have first : property
              (SourceCurrentConjunctionRequirementRows.nextRow handle before.storage).state.requirements.physical.heap := by
            rw [SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap]
            exact known
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state,
                SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using first
          | done row storage =>
              have clean : property storage.requirements.physical.heap := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact clean
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact clean

/-- The actual finite run derives the heap predicate at every terminal outcome from current inputs. -/
private theorem run_heap (property : Heap → Prop)
    (sampleKeeps : ∀ h budget (nodes : List Node) (before : Physical), Ready before →
      Values before.heap nodes → property before.heap →
      property (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap)
    (forceKeeps : ∀ p h handle (before : SourceCurrentConjunctionRequirementCells.State Symbol Formula),
      Ready before.physical → SourceCurrentConjunctionRequirementCellsValues.Invariant before →
      property before.physical.heap →
      property (SourceCurrentConjunctionRequirementCells.force p h handle before).state.physical.heap)
    {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (values : Invariant before) (known : property before.storage.requirements.physical.heap) :
    property outcome.state.storage.requirements.physical.heap := by
  revert values known
  induction actual with
  | @failed before after fault advanced =>
      intro values known
      simpa only [advanced, Outcome.state] using step_heap property sampleKeeps forceKeeps p h before values known
  | @drained before after advanced =>
      intro values known
      simpa only [advanced, Outcome.state] using step_heap property sampleKeeps forceKeeps p h before values known
  | @more before middle outcome advanced tail ih =>
      intro values known
      have current : Invariant middle := by
        simpa only [advanced, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have clean : property middle.storage.requirements.physical.heap := by
        simpa only [advanced, Outcome.state] using step_heap property sampleKeeps forceKeeps p h before values known
      exact ih current clean

/-- Original initialization derives the heap predicate without a future trace or heap. -/
private theorem explore_heap (property : Heap → Prop)
    (sampleKeeps : ∀ h budget (nodes : List Node) (before : Physical), Ready before →
      Values before.heap nodes → property before.heap →
      property (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap)
    (forceKeeps : ∀ p h handle (before : SourceCurrentConjunctionRequirementCells.State Symbol Formula),
      Ready before.physical → SourceCurrentConjunctionRequirementCellsValues.Invariant before →
      property before.physical.heap →
      property (SourceCurrentConjunctionRequirementCells.force p h handle before).state.physical.heap)
    (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (known : property before.heap) (available : Available before.heap start) :
    property (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state.storage.requirements.physical.heap :=
  run_heap property sampleKeeps forceKeeps (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available) known

/-- Actual exploration retains causal Mu observations from the current physical state. -/
theorem explore_guard_heap (annotation : Guard → Prop) (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (known : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.heap)
    (available : Available before.heap start) :
    SourceCurrentConstrainedCapGuardHeap.Heap annotation
      (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state.storage.requirements.physical.heap :=
  explore_heap (SourceCurrentConstrainedCapGuardHeap.Heap annotation)
    (fun h budget nodes before ready available known =>
      SourceCurrentConjunctionDemandAnnotations.sample_guard_heap annotation h budget nodes before
        ready.semantic ready.costs available known)
    (SourceCurrentConjunctionRequirementCellsGuardArity.force_guard_heap annotation)
    p h budget start before ready known available

end MicroCFTA.SourceCurrentConjunctionSharedWorklistGuardArity

namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistGuardArity
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
variable {Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual exploration retains whole-record arity without a closed-query premise. -/
theorem explore_arity_heap (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (known : SourcePruningEnumerationArityOrigins.Heap before.heap)
    (available : Available before.heap start) :
    SourcePruningEnumerationArityOrigins.Heap
      (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state.storage.requirements.physical.heap :=
  explore_heap SourcePruningEnumerationArityOrigins.Heap
    (fun h budget nodes before ready available known =>
      SourceCurrentConjunctionDemandAnnotations.sample_arity_heap h budget nodes before
        ready.semantic ready.costs available known)
    SourceCurrentConjunctionRequirementCellsGuardArity.force_arity_heap
    p h budget start before ready known available

end MicroCFTA.SourceCurrentConjunctionSharedWorklistGuardArity

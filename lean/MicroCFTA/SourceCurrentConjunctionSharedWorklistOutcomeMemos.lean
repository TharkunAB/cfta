import MicroCFTA.SourceCurrentConjunctionSharedWorklistValues
import MicroCFTA.SourceCurrentConjunctionRequirementCellsOutcomeMemos
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalOutcomeMemos
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes

/-!
# Global receipts at every actual shared-worklist endpoint

Selected sampling and requirement forcing retain their complete ordered
memo receipts, including terminal faults. Row preparation records its
actual fault or publication and retains the same global tables. The actual
finite run derives each intermediate bundle from current resident values.
No closedness, future receipt, or successful outcome is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistOutcomeMemos
open Cache
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistRun (Run explore explore_graph)
open SourceCurrentConjunctionSharedWorklistValues (Invariant)
open SourceCurrentConjunctionTuplePullTotalOutcomeMemos (SampleReads)
open SourceCurrentConjunctionRequirementCellsOutcomeMemos (ForceReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Task" => SourceCurrentConjunctionSharedWorklistStep.Task Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A visit records its actual skip or the complete selected sample, including a failed sample. -/
inductive VisitReads (h : Nat) (nodes : List Node) (rest : List Task) (before : WorkState) :
    Memos → Memos → Prop where
  | empty (empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty = true) : VisitReads h nodes rest before memos memos
  | skip (nonempty : nodes.any SourceCurrentConjunctionRequirements.isEmpty = false)
      (skipped : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget (queryTable before.table) nodes = true) :
      VisitReads h nodes rest before memos memos
  | sample (nonempty : nodes.any SourceCurrentConjunctionRequirements.isEmpty = false)
      (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget (queryTable before.table) nodes = false)
      (calls : SampleReads h before.budget nodes before.storage.requirements.physical memos saved) :
      VisitReads h nodes rest before memos saved

/-- A transition retains the literal branch and force-before-visit order on every outcome. -/
inductive StepReads (p h : Nat) (before : WorkState) : Memos → Memos → Prop where
  | drained (pending : before.pending = []) : StepReads p h before memos memos
  | nodes (pending : before.pending = .nodes nodes :: rest) (calls : VisitReads h nodes rest before memos saved) :
      StepReads p h before memos saved
  | requirements_nil (pending : before.pending = .requirements [] :: rest) : StepReads p h before memos memos
  | requirement_failed (pending : before.pending = .requirements (handle :: handles) :: rest)
      (forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements = .failed fault cells)
      (calls : ForceReads p h handle before.storage.requirements (.failed fault cells) memos saved) :
      StepReads p h before memos saved
  | requirement_done (pending : before.pending = .requirements (handle :: handles) :: rest)
      (forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements = .done nodes cells)
      (first : ForceReads p h handle before.storage.requirements (.done nodes cells) memos middle)
      (last : VisitReads h nodes (.requirements handles :: rest)
        {before with storage := {before.storage with requirements := cells}} middle saved) :
      StepReads p h before memos saved
  | rows_failed (pending : before.pending = .rows handle :: rest)
      (advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage = .failed fault storage) :
      StepReads p h before memos memos
  | rows_none (pending : before.pending = .rows handle :: rest)
      (advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage = .done none storage) :
      StepReads p h before memos memos
  | rows_live (pending : before.pending = .rows handle :: rest)
      (advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage = .done (some (handles, tail)) storage) :
      StepReads p h before memos memos

/-- The actual finite execution retains every transition receipt, including its terminal fault. -/
inductive RunReads : {p h : Nat} → {before : WorkState} → {outcome : Outcome Symbol FullSyntax.Formula} →
    Run p h before outcome → Memos → Memos → Prop where
  | failed {p h : Nat} {before after : WorkState} {fault : Fault Symbol FullSyntax.Formula}
      {actual : step p h before = .failed fault after} {memos saved : Memos}
      (calls : StepReads p h before memos saved) : RunReads (.failed actual) memos saved
  | drained {p h : Nat} {before after : WorkState} {actual : step p h before = .done .drained after}
      {memos saved : Memos} (calls : StepReads p h before memos saved) : RunReads (.drained actual) memos saved
  | more {p h : Nat} {before middle : WorkState} {outcome : Outcome Symbol FullSyntax.Formula}
      {actual : step p h before = .done .more middle} {tail : Run p h middle outcome} {memos current saved : Memos}
      (first : StepReads p h before memos current) (rest : RunReads tail current saved) :
      RunReads (.more actual tail) memos saved

/-- Original exploration uses its internally derived actual finite execution graph. -/
def ExploreReads (p h budget : Nat) (start : Node) (before : Physical) (memos saved : Memos) : Prop :=
  RunReads (explore_graph p h budget start before) memos saved

/-- Every actual visit derives a coherent returned bundle, including a terminal sample fault. -/
theorem visit_memos (h : Nat) (nodes : List Node) (rest : List Task) (before : WorkState)
    (ready : Ready before.storage.requirements.physical)
    (available : Values before.storage.requirements.physical.heap nodes) (memos : Memos)
    (valid : Valid before.storage.requirements.physical.heap memos) :
    ∃ saved, VisitReads h nodes rest before memos saved ∧
      Valid (visit h nodes rest before).state.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact ⟨memos, .empty empty, valid, extends_refl _, rfl⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact ⟨memos, .skip empty skipped, valid, extends_refl _, rfl⟩
      | false =>
          obtain ⟨saved, calls, coherent, retained, same⟩ :=
            SourceCurrentConjunctionTuplePullTotalOutcomeMemos.sample_memos h before.budget nodes
              before.storage.requirements.physical ready available memos valid
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              have finalValid : Valid physical.heap saved := by
                simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using coherent
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact ⟨saved, .sample empty skipped calls, finalValid, retained, same⟩
          | done result physical =>
              have finalValid : Valid physical.heap saved := by
                simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using coherent
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact ⟨saved, .sample empty skipped calls, finalValid, retained, same⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      exact ⟨saved, .sample empty skipped calls, finalValid, retained, same⟩
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      exact ⟨saved, .sample empty skipped calls, finalValid, retained, same⟩

/-- Every actual transition derives ordered calls and validity at its exact reached physical heap. -/
theorem step_memos (p h : Nat) (before : WorkState) (values : Invariant before) (memos : Memos)
    (valid : Valid before.storage.requirements.physical.heap memos) :
    ∃ saved, StepReads p h before memos saved ∧ Valid (step p h before).state.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact ⟨memos, .drained pending, valid, extends_refl _, rfl⟩
  | cons task rest =>
      cases task with
      | nodes nodes =>
          obtain ⟨saved, calls, coherent, retained, same⟩ := visit_memos h nodes rest before values.ready
            (values.pending nodes (by rw [pending]; exact List.mem_cons_self)) memos valid
          rw [step_nodes p h before nodes rest pending]
          exact ⟨saved, .nodes pending calls, coherent, retained, same⟩
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact ⟨memos, .requirements_nil pending, valid, extends_refl _, rfl⟩
          | cons handle handles =>
              obtain ⟨middle, calls, coherent, retained, same⟩ :=
                SourceCurrentConjunctionRequirementCellsOutcomeMemos.force_memos p h handle
                  before.storage.requirements values.ready values.cells memos valid
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  have first : ForceReads p h handle before.storage.requirements (.failed fault cells) memos middle := by
                    simpa only [forced] using calls
                  have finalValid : Valid cells.physical.heap middle := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using coherent
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact ⟨middle, .requirement_failed pending forced first, finalValid, retained, same⟩
              | done nodes cells =>
                  have first : ForceReads p h handle before.storage.requirements (.done nodes cells) memos middle := by
                    simpa only [forced] using calls
                  have currentValid : Valid cells.physical.heap middle := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using coherent
                  have own := SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                    before.storage.requirements values.ready values.cells
                  have current : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧ Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using own
                  obtain ⟨saved, last, finalValid, finalRetained, finalSame⟩ :=
                    visit_memos h nodes (.requirements handles :: rest)
                      {before with storage := {before.storage with requirements := cells}}
                      current.1.ready current.2.2 middle currentValid
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact ⟨saved, .requirement_done pending forced first last, finalValid,
                    extends_trans retained finalRetained, finalSame.trans same⟩
      | rows handle =>
          have preserved := SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap handle before.storage
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              have sameHeap : storage.requirements.physical.heap = before.storage.requirements.physical.heap := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using preserved
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact ⟨memos, .rows_failed pending advanced, sameHeap.symm ▸ valid, extends_refl _, rfl⟩
          | done row storage =>
              have sameHeap : storage.requirements.physical.heap = before.storage.requirements.physical.heap := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using preserved
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact ⟨memos, .rows_none pending advanced, sameHeap.symm ▸ valid, extends_refl _, rfl⟩
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact ⟨memos, .rows_live pending advanced, sameHeap.symm ▸ valid, extends_refl _, rfl⟩

/-- The actual finite run derives coherent global receipts for its complete outcome. -/
theorem run_memos {p h : Nat} {before : WorkState} {outcome : Outcome Symbol FullSyntax.Formula}
    (actual : Run p h before outcome) (values : Invariant before) (memos : Memos)
    (valid : Valid before.storage.requirements.physical.heap memos) :
    ∃ saved, RunReads actual memos saved ∧ Valid outcome.state.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  revert values memos valid
  induction actual with
  | @failed before after fault advanced =>
      intro values memos valid
      obtain ⟨saved, calls, coherent, retained, same⟩ := step_memos p h before values memos valid
      refine ⟨saved, .failed (actual := advanced) calls, ?_, retained, same⟩
      simpa only [advanced, Outcome.state] using coherent
  | @drained before after advanced =>
      intro values memos valid
      obtain ⟨saved, calls, coherent, retained, same⟩ := step_memos p h before values memos valid
      refine ⟨saved, .drained (actual := advanced) calls, ?_, retained, same⟩
      simpa only [advanced, Outcome.state] using coherent
  | @more before middle outcome advanced tail ih =>
      intro values memos valid
      obtain ⟨currentMemo, first, coherent, retained, same⟩ := step_memos p h before values memos valid
      have current : Invariant middle := by
        simpa only [advanced, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have currentValid : Valid middle.storage.requirements.physical.heap currentMemo := by
        simpa only [advanced, Outcome.state] using coherent
      obtain ⟨saved, last, finalValid, finalRetained, finalSame⟩ := ih current currentMemo currentValid
      exact ⟨saved, .more (actual := advanced) first last, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

/-- Current original inputs derive the exact returned exploration bundle without a future receipt. -/
theorem explore_memos (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, ExploreReads p h budget start before memos saved ∧
      Valid (explore p h budget start before).state.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query :=
  run_memos (explore_graph p h budget start before)
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available) memos valid

end MicroCFTA.SourceCurrentConjunctionSharedWorklistOutcomeMemos

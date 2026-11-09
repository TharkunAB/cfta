import MicroCFTA.SourceCurrentUnionNormalProjectionGate
import MicroCFTA.SourceCurrentConjunctionTuplePullHeapEffects
import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker

/-!
# Union normality through literal shared conjunction work

Sampling and deferred projections retain normal union records. Row
publication changes no value heap. The finite shared run preserves these
facts at its actual successful or failed endpoint. No future normality or
completed execution is an input.
-/
namespace MicroCFTA.SourceCurrentSharedUnionNormalConjunction
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
open SourceCurrentConjunctionSharedWorklistStep
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State
section Generic
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection (p h : Nat) (job : SourceCurrentConjunctionRowsWorker.Job Symbol Formula)
    (before : Physical Symbol Formula) (normal : UnionNormal before.heap) :
    UnionNormal (SourceCurrentConjunctionRequirementPull.projection p h job before).state.heap := by
  rcases job with ⟨values, path⟩
  have retained := SourceCurrentUnionNormalProjectionGate.forest p h (path.map Int.ofNat) values before.heap normal
  cases actual : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) values before.heap <;>
    simpa only [SourceCurrentConjunctionRequirementPull.projection,
      SourceCurrentConjunctionRowsWorker.projections, actual, SourceCurrentConjunctionRowsWorker.Outcome.bind,
      SourceCurrentConjunctionRowsWorker.Outcome.state, SourceCurrentRequiredUnionNormalRead.StoppedNormal]
      using retained

private theorem pull (p h : Nat) (cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula)
    (before : Physical Symbol Formula) (normal : UnionNormal before.heap) :
    UnionNormal (SourceCurrentConjunctionRequirementPull.run p h cursor before).state.heap := by
  rcases cursor with ⟨jobs, collected⟩
  induction jobs generalizing collected before with
  | nil => exact normal
  | cons job rest ih =>
      have first := projection p h job before normal
      cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before after fault actual]
          simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
      | done value after =>
          have afterNormal : UnionNormal after.heap := by
            simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
          cases empty : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              rw [SourceCurrentConjunctionRequirementPull.run_step]
              simpa only [SourceCurrentConjunctionRequirementPull.step, actual,
                SourceCurrentConjunctionRowsWorker.Outcome.bind, empty, ite_true,
                SourceCurrentConjunctionRowsWorker.Outcome.state] using afterNormal
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before after value actual empty]
              exact ih (before := after) (collected := collected ++ [value]) afterNormal

private theorem force (p h handle : Nat) (before : SourceCurrentConjunctionRequirementCells.State Symbol Formula)
    (normal : UnionNormal before.physical.heap) :
    UnionNormal (SourceCurrentConjunctionRequirementCells.force p h handle before).state.physical.heap := by
  cases found : SourceCurrentConjunctionRequirementCells.lookup handle before with
  | none =>
      rw [SourceCurrentConjunctionRequirementCells.force_step,
        SourceCurrentConjunctionRequirementCells.forceStep_missing p h handle before found]
      exact normal
  | some cell =>
      cases cell with
      | column nodes =>
          rw [SourceCurrentConjunctionRequirementCells.force_step]
          simp only [SourceCurrentConjunctionRequirementCells.forceStep, found]
          exact normal
      | done nodes =>
          rw [SourceCurrentConjunctionRequirementCells.force_hit p h handle nodes before found]
          exact normal
      | pending cursor =>
          have retained := pull p h cursor before.physical normal
          cases actual : SourceCurrentConjunctionRequirementCells.force p h handle before with
          | done nodes after =>
              have same := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
              rw [same] at retained
              exact retained
          | failed diagnostic after =>
              obtain ⟨stopped, fault, _, same, _⟩ :=
                SourceCurrentConjunctionRequirementCellsExecution.force_pending_failed found actual
              rw [same] at retained
              exact retained

variable [DecidableEq Symbol]

private theorem visit_normal (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState Symbol Formula) (normal : UnionNormal before.storage.requirements.physical.heap) :
    UnionNormal (visit h nodes rest before).state.storage.requirements.physical.heap := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true => rw [visit_empty h nodes rest before empty]; exact normal
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true => rw [visit_skip h nodes rest before empty skipped]; exact normal
      | false =>
          have first := SourceCurrentConjunctionTuplePullHeapEffects.sample_preserves UnionNormal h before.budget nodes
            before.storage.requirements.physical normal
            (fun heap node _ heapNormal => SourceCurrentRequiredUnionNormalRead.nodeEdges h node heap heapNormal)
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state, Outcome.state, withPhysical] using first
          | done result physical =>
              have current : UnionNormal physical.heap := by
                simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]; exact current
              | fit tuples =>
                  cases tuples with
                  | nil => rw [visit_zero h nodes rest before physical empty skipped sampled]; exact current
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]; exact current

private theorem step_normal (p h : Nat) (before : WorkState Symbol Formula)
    (normal : UnionNormal before.storage.requirements.physical.heap) :
    UnionNormal (step p h before).state.storage.requirements.physical.heap := by
  cases pending : before.pending with
  | nil => rw [step_nil p h before pending]; exact normal
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_normal h nodes rest before normal
      | requirements handles =>
          cases handles with
          | nil => rw [step_requirements_nil p h before rest pending]; exact normal
          | cons handle handles =>
              have first := force p h handle before.storage.requirements normal
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state, Outcome.state] using first
              | done nodes cells =>
                  have current : UnionNormal cells.physical.heap := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using first
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_normal h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} current
      | rows handle =>
          have first : UnionNormal (SourceCurrentConjunctionRequirementRows.nextRow handle before.storage).state.requirements.physical.heap := by
            rw [SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap]
            exact normal
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state, Outcome.state] using first
          | done row storage =>
              have current : UnionNormal storage.requirements.physical.heap := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
              cases row with
              | none => rw [step_rows_none p h handle before rest storage pending advanced]; exact current
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]; exact current

private theorem run_normal {p h : Nat} {before : WorkState Symbol Formula} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (normal : UnionNormal before.storage.requirements.physical.heap) :
    UnionNormal outcome.state.storage.requirements.physical.heap := by
  revert normal
  induction actual with
  | @failed before after fault advanced =>
      intro normal
      simpa only [advanced, Outcome.state] using step_normal p h before normal
  | @drained before after advanced =>
      intro normal
      simpa only [advanced, Outcome.state] using step_normal p h before normal
  | @more before middle outcome advanced tail ih =>
      intro normal
      apply ih
      simpa only [advanced, Outcome.state] using step_normal p h before normal

private theorem explore (p h budget : Nat) (query : Node) (before : Physical Symbol Formula)
    (normal : UnionNormal before.heap) :
    UnionNormal (SourceCurrentConjunctionSharedWorklistRun.explore p h budget query before).state.storage.requirements.physical.heap :=
  run_normal (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget query before) normal

end Generic

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Every raw shared call retains normal union records at its exact returned snapshot. -/
theorem raw_call (p h budget : Nat) (memo : Memo) (query : Node)
    (before : Physical Symbol FullSyntax.Formula) (normal : UnionNormal before.heap) :
    UnionNormal (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical.heap := by
  rw [SourceCurrentConjunctionSharedWorkerEffects.call_state]
  split
  · exact normal
  · rw [SourceCurrentConjunctionSharedWorkerEffects.decision_state]
    split
    · exact explore p h budget query before normal
    · exact normal

/-- The checked adapter retains the same normal heap on both successful and failed calls. -/
theorem call (p h budget : Nat) (memo : Memo) (query : Node) (before : Checked width)
    (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedConjunctionWorker.call p h budget query before memo).state.native.machine.heap := by
  rw [SourceCurrentAllocatedSharedConjunctionWorker.call_state,
    SourceCurrentAllocatedSharedConjunctionWorker.call_snapshot]
  change UnionNormal (SourceCurrentConjunctionSharedWorker.call p h budget memo query
    (SourceCurrentAllocatedNativeEffects.physical before)).state.storage.requirements.physical.heap
  exact raw_call p h budget memo query (SourceCurrentAllocatedNativeEffects.physical before) normal

end MicroCFTA.SourceCurrentSharedUnionNormalConjunction

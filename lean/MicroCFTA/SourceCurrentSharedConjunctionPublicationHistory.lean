import MicroCFTA.SourceCurrentRequiredPublicationHistory
import MicroCFTA.SourceCurrentConjunctionTuplePullReadTrace
import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementCellsValues
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes
import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects

/-!
# Causal publication through successful shared conjunction calls

The proof follows actual demanded samples and shared-cell projections.
Each projection supplies its own publication interval. Private row
preparation retains the value heap. Finite successful execution composes
these intervals at the same physical endpoints. The proof needs current
readiness and resident inputs. It needs no global memo validity or closed
input premise. Failed terminal reads remain outside this successful law.
-/
namespace MicroCFTA.SourceCurrentSharedConjunctionPublicationHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistValues (Invariant)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Job" => SourceCurrentConjunctionRowsWorker.Job Symbol FullSyntax.Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Task" => SourceCurrentConjunctionSharedWorklistStep.Task Symbol FullSyntax.Formula
local notation "Cursor" => SourceCurrentConjunctionRequirementPull.Cursor Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Pull" => SourceCurrentConjunctionRequirementPull.run
local notation "projection" => SourceCurrentConjunctionRequirementPull.projection
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem exposures {nodes : List Node} {before after : Heap}
    {rows : List (List (EdgeValue Symbol Guard))}
    (actual : SourceCurrentConjunctionCompletionReads.Exposures nodes before rows after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before nodes) :
    Nonempty (History before after) := by
  induction actual with
  | nil => exact ⟨.refl _⟩
  | cons first rest ih =>
      obtain ⟨head⟩ := SourceCurrentRequiredPublicationHistory.read first semantic costs
        (available _ List.mem_cons_self)
      have effects := SourceEqualityProjectionCosts.read_effects first semantic costs
        (available _ List.mem_cons_self)
      obtain ⟨tail⟩ := ih effects.2.1 effects.2.2.1
        (fun node member => effects.1.available node (available node (List.mem_cons_of_mem _ member)))
      exact ⟨.trans head tail⟩

private theorem projected {p h : Nat} {job : Job} {before after : Physical} {node : Node}
    (actual : projection p h job before = .done node after)
    (ready : Ready before) (available : Values before.heap job.1) :
    Nonempty (History before.heap after.heap) := by
  rcases job with ⟨forest,path⟩
  cases read : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
  | pending | unresolved | exhausted =>
      simp only [SourceCurrentConjunctionRequirementPull.projection,
        SourceCurrentConjunctionRowsWorker.projections,read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
      cases actual
  | done value heap =>
      simp only [SourceCurrentConjunctionRequirementPull.projection,
        SourceCurrentConjunctionRowsWorker.projections,read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind,List.headD_cons] at actual
      cases actual
      exact SourceCurrentRequiredPublicationHistory.forest
        (SourceEqualityProjectionWorkerSound.forest_graph _ _ _ _ _ _ _ read)
        ready.semantic ready.costs available

private theorem cursor_run (p h : Nat) : ∀ (jobs : List Job) (collected : List Node)
    (before : Physical), Ready before → (∀ job ∈ jobs, Values before.heap job.1) →
    ∀ (nodes : List Node) (after : Physical),
      Pull p h ⟨jobs,collected⟩ before = .done nodes after →
      Nonempty (History before.heap after.heap) := by
  intro jobs
  induction jobs with
  | nil =>
      intro collected before _ready _available nodes after actual
      rw [SourceCurrentConjunctionRequirementPull.run_nil] at actual
      cases actual
      exact ⟨.refl _⟩
  | cons job rest ih =>
      intro collected before ready available nodes after actual
      cases read : projection p h job before with
      | failed fault middle =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before middle fault read] at actual
          cases actual
      | done value middle =>
          obtain ⟨head⟩ := projected read ready (available job List.mem_cons_self)
          have kept : Effects before middle := by
            simpa only [read,SourceCurrentConjunctionRowsWorker.Outcome.state] using
              SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job before ready
                (available job List.mem_cons_self)
          cases empty : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              rw [SourceCurrentConjunctionRequirementPull.run_step] at actual
              simp only [SourceCurrentConjunctionRequirementPull.step,read,
                SourceCurrentConjunctionRowsWorker.Outcome.bind,empty,ite_true] at actual
              cases actual
              exact ⟨head⟩
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before middle value read empty] at actual
              obtain ⟨tail⟩ := ih (collected ++ [value]) middle kept.ready
                (fun next member node included => kept.keeps.available node
                  (available next (List.mem_cons_of_mem _ member) node included)) nodes after actual
              exact ⟨.trans head tail⟩

private theorem force {p h handle : Nat} {before after : Cells} {nodes : List Node}
    (actual : SourceCurrentConjunctionRequirementCells.force p h handle before = .done nodes after)
    (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before) :
    Nonempty (History before.physical.heap after.physical.heap) := by
  cases found : SourceCurrentConjunctionRequirementCells.lookup handle before with
  | none =>
      rw [SourceCurrentConjunctionRequirementCells.force_step] at actual
      simp only [SourceCurrentConjunctionRequirementCells.forceStep,found] at actual
      cases actual
  | some cell =>
      cases cell with
      | done cached =>
          rw [SourceCurrentConjunctionRequirementCells.force_hit p h handle cached before found] at actual
          cases actual
          exact ⟨.refl _⟩
      | column column =>
          rw [SourceCurrentConjunctionRequirementCells.force_step] at actual
          simp only [SourceCurrentConjunctionRequirementCells.forceStep,found] at actual
          cases actual
          exact ⟨.refl _⟩
      | pending cursor =>
          exact cursor_run p h cursor.pending cursor.collected before.physical ready
            (values handle (.pending cursor) found).2 nodes after.physical
            (SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual)

variable [DecidableEq Symbol]

private theorem visit_history {h : Nat} {nodes : List Node} {rest : List Task}
    {before after : WorkState} {event : Event}
    (actual : visit h nodes rest before = .done event after)
    (ready : Ready before.storage.requirements.physical)
    (available : Values before.storage.requirements.physical.heap nodes) :
    Nonempty (History before.storage.requirements.physical.heap after.storage.requirements.physical.heap) := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty] at actual
      cases actual
      exact ⟨.refl _⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped] at actual
          cases actual
          exact ⟨.refl _⟩
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled] at actual
              cases actual
          | done result physical =>
              obtain ⟨reads,rows,readTrace,included⟩ := SourceCurrentConjunctionTuplePullReadTrace.sample_reads
                h before.budget nodes before.storage.requirements.physical physical result sampled
              have interval := exposures readTrace ready.semantic ready.costs
                (fun node member => available node (included node member))
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled] at actual
                  cases actual
                  exact interval
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled] at actual
                      cases actual
                      exact interval
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled] at actual
                      cases actual
                      exact interval

private theorem step_history {p h : Nat} {before after : WorkState} {event : Event}
    (actual : step p h before = .done event after) (values : Invariant before) :
    Nonempty (History before.storage.requirements.physical.heap after.storage.requirements.physical.heap) := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending] at actual
      cases actual
      exact ⟨.refl _⟩
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending] at actual
          exact visit_history actual values.ready
            (values.pending nodes (by rw [pending]; exact List.mem_cons_self))
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending] at actual
              cases actual
              exact ⟨.refl _⟩
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced] at actual
                  cases actual
              | done nodes cells =>
                  obtain ⟨first⟩ := force forced values.ready values.cells
                  have current : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧ Values cells.physical.heap nodes := by
                    simpa only [forced,SourceCurrentConjunctionRequirementCells.Outcome.state] using
                      SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                        before.storage.requirements values.ready values.cells
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced] at actual
                  obtain ⟨last⟩ := visit_history actual current.1.ready current.2.2
                  exact ⟨.trans first last⟩
      | rows handle =>
          have same := SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap handle before.storage
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced] at actual
              cases actual
          | done row storage =>
              rw [advanced] at same
              change storage.requirements.physical.heap = before.storage.requirements.physical.heap at same
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced] at actual
                  cases actual
                  rw [same]
                  exact ⟨.refl _⟩
              | some pair =>
                  rcases pair with ⟨handles,tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced] at actual
                  cases actual
                  rw [same]
                  exact ⟨.refl _⟩

private def Completed (before : Heap) : Outcome Symbol FullSyntax.Formula → Prop
  | .failed _ _ => True
  | .done _ after => Nonempty (History before after.storage.requirements.physical.heap)

private theorem run_history {p h : Nat} {before : WorkState} {outcome : Outcome Symbol FullSyntax.Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (values : Invariant before) : Completed before.storage.requirements.physical.heap outcome := by
  revert values
  induction actual with
  | failed => intro _; trivial
  | drained advanced => intro values; exact step_history advanced values
  | @more before middle outcome advanced tail ih =>
      intro values
      obtain ⟨head⟩ := step_history advanced values
      have current : Invariant middle := by
        simpa only [advanced,Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have later := ih current
      cases outcome with
      | failed => trivial
      | done event after =>
          obtain ⟨last⟩ := later
          exact ⟨.trans head last⟩

variable [DecidableEq Node]

private theorem decision {p h budget : Nat} {query : Node} {before : Physical}
    {answer : Bool} {after : WorkState}
    (actual : SourceCurrentConjunctionSharedWorker.decision p h budget query before = .done answer after)
    (ready : Ready before) (available : Available before.heap query) :
    Nonempty (History before.heap after.storage.requirements.physical.heap) := by
  cases closedInput : SourceCurrentConjunctionWorklist.closed query with
  | false =>
      rw [SourceCurrentConjunctionSharedWorker.decision_open p h budget query before closedInput] at actual
      cases actual
      exact ⟨.refl _⟩
  | true =>
      cases explored : SourceCurrentConjunctionSharedWorklistRun.explore p h budget query before with
      | failed fault middle =>
          simp only [SourceCurrentConjunctionSharedWorker.decision,closedInput,ite_true,explored] at actual
          cases actual
      | done event middle =>
          have interval := run_history
            (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget query before)
            (SourceCurrentConjunctionSharedWorklistValues.initial_values budget query before ready available)
          rw [explored] at interval
          have same := SourceCurrentConjunctionSharedWorkerEffects.decision_state p h budget query before
          simp only [actual,closedInput,ite_true,explored,
            SourceCurrentConjunctionSharedWorker.Outcome.state,Outcome.state] at same
          rw [same]
          exact interval

/-- A successful literal shared call derives its own causal publication interval. -/
theorem call {p h budget : Nat} {memo saved : Memo} {query : Node} {before : Physical}
    {answer : Bool} {after : WorkState}
    (actual : SourceCurrentConjunctionSharedWorker.call p h budget memo query before = .done (answer,saved) after)
    (ready : Ready before) (available : Available before.heap query) :
    Nonempty (History before.heap after.storage.requirements.physical.heap) := by
  cases found : memo query.referenceOf with
  | some entry =>
      rcases entry with ⟨original,value⟩
      simp only [SourceCurrentConjunctionSharedWorker.call,found] at actual
      cases actual
      exact ⟨.refl _⟩
  | none =>
      simp only [SourceCurrentConjunctionSharedWorker.call,found] at actual
      cases observed : SourceCurrentConjunctionSharedWorker.decision p h budget query before with
      | failed fault middle =>
          simp only [observed,SourceCurrentConjunctionSharedWorker.Outcome.bind] at actual
          cases actual
      | done value middle =>
          simp only [observed,SourceCurrentConjunctionSharedWorker.Outcome.bind] at actual
          cases actual
          exact decision observed ready available

end MicroCFTA.SourceCurrentSharedConjunctionPublicationHistory

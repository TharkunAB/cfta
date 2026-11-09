import MicroCFTA.SourceCurrentConjunctionRequirementCellsCompletion
import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionProjectionResources

/-!
# Current numeric bounds for one shared requirement cell

The current pending jobs determine the maximum path depth, forest width,
and number of projections. Their fixed scalar schedule bounds every actual
consumed prefix. The first Empty result retains its own physical endpoint.
Cached cells and columns perform no projection. The bounds do not depend
on a remaining tuple budget or a future completion witness.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Physical Job)
open SourceCurrentConjunctionRequirementCells
open SourceCurrentConjunctionRequirementPull (Cursor projection)
open SourceCurrentConjunctionProjectionResources (step jobsBound workerFuel)
open SourceCurrentProjectionUnionResources (readFuel)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- Only a pending cell has projection jobs. -/
def pendingJobs (handle : Nat) (before : Cells) : List (Job Symbol Formula) :=
  match lookup handle before with
  | some (.pending cursor) => cursor.pending
  | _ => []

/-- The literal current paths determine the maximum projection depth. -/
def depth (jobs : List (Job Symbol Formula)) : Nat :=
  jobs.foldr (fun job bound => max job.2.length bound) 0

/-- The literal current forests determine the maximum operand count. -/
def width (jobs : List (Job Symbol Formula)) : Nat :=
  jobs.foldr (fun job bound => max job.1.length bound) 0

/-- The current job count fixes the complete scalar schedule. -/
def forecast (handle : Nat) (before : Cells) (resource : Nat) : Nat :=
  let jobs := pendingJobs handle before
  jobsBound (depth jobs) (width jobs) jobs.length resource

/-- The current paths determine one shared projection worker ceiling. -/
def projectionFuel (handle : Nat) (before : Cells) : Nat :=
  workerFuel (depth (pendingJobs handle before))

/-- The final scalar schedule determines one shared recursive reader ceiling. -/
def readerFuel (handle : Nat) (before : Cells) (resource : Nat) : Nat :=
  readFuel (forecast handle before resource)

private theorem maximum_member (measure : Job Symbol Formula → Nat)
    (jobs : List (Job Symbol Formula)) (job : Job Symbol Formula) (member : job ∈ jobs) :
    measure job ≤ jobs.foldr (fun next bound => max (measure next) bound) 0 := by
  induction jobs with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection_bound {p h : Nat} (job : Job Symbol Formula)
    (before after : Physical Symbol Formula) (value : Node) (resource maxDepth maxWidth : Nat)
    (ready : Ready before) (available : Values before.heap job.1) (closed : ClosedValues job.1)
    (fits : Fits resource before.heap) (paths : job.2.length ≤ maxDepth) (counts : job.1.length ≤ maxWidth)
    (actual : projection p h job before = .done value after) :
    Fits (step maxDepth maxWidth resource) after.heap ∧
      ∀ P H, workerFuel maxDepth ≤ P → readFuel (step maxDepth maxWidth resource) ≤ H →
        projection P H job before = .done value after := by
  rcases job with ⟨forest, path⟩
  change path.length ≤ maxDepth at paths
  change forest.length ≤ maxWidth at counts
  cases read : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
  | done output heap =>
      have same : output = value ∧ (⟨heap, before.equality⟩ : Physical Symbol Formula) = after := by
        simpa only [projection, SourceCurrentConjunctionRowsWorker.projections, read,
          SourceCurrentConjunctionRowsWorker.Outcome.bind, List.headD_cons,
          SourceCurrentConjunctionRowsWorker.Outcome.done.injEq] using actual
      obtain ⟨sameValue, sameState⟩ := same
      subst output
      subst after
      have graph := SourceEqualityProjectionWorkerSound.forest_graph p h (path.map Int.ofNat)
        forest before.heap value heap read
      have checked := SourceCurrentProjectionInitialResources.forest_bound _ graph resource
        ready.semantic ready.costs available
        (SourceCurrentConjunctionProjectionResources.closed_forest_domain _ forest before.heap ready.semantic available closed) fits
      have increase := SourceCurrentConjunctionProjectionResources.forestBound_le_step
        (resource := resource) (path.map Int.ofNat) (by simpa only [List.length_map] using paths) counts
      refine ⟨checked.1.mono increase, ?_⟩
      intro P H enoughP enoughH
      have works : SourceCurrentProjectionNumericReplay.workFuel (path.map Int.ofNat) ≤ P := by
        simp only [SourceCurrentProjectionNumericReplay.workFuel, List.length_map]
        change 2 * maxDepth + 1 ≤ P at enoughP
        omega
      have reads := Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono increase) enoughH
      have replay := SourceCurrentProjectionNumericReplay.forest_replay checked.2 P H works reads
      simp only [projection, SourceCurrentConjunctionRowsWorker.projections, replay,
        SourceCurrentConjunctionRowsWorker.Outcome.bind, List.headD_cons]
  | pending key heap | unresolved name heap | exhausted limit heap =>
      simp only [projection, SourceCurrentConjunctionRowsWorker.projections, read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
      cases actual

private theorem run_bound (jobs : List (Job Symbol Formula)) (collected : List Node)
    (before : Physical Symbol Formula) (resource maxDepth maxWidth : Nat)
    (ready : Ready before)
    (inputs : ∀ job ∈ jobs, Values before.heap job.1 ∧ ClosedValues job.1)
    (fits : Fits resource before.heap)
    (depths : ∀ job ∈ jobs, job.2.length ≤ maxDepth)
    (widths : ∀ job ∈ jobs, job.1.length ≤ maxWidth)
    {p h : Nat} {nodes : List Node} {after : Physical Symbol Formula}
    (actual : SourceCurrentConjunctionRequirementPull.run p h ⟨jobs, collected⟩ before = .done nodes after) :
    Fits (jobsBound maxDepth maxWidth jobs.length resource) after.heap ∧
      ∀ P H, workerFuel maxDepth ≤ P → readFuel (jobsBound maxDepth maxWidth jobs.length resource) ≤ H →
        SourceCurrentConjunctionRequirementPull.run P H ⟨jobs, collected⟩ before = .done nodes after := by
  induction jobs generalizing collected before resource nodes after with
  | nil =>
      rw [SourceCurrentConjunctionRequirementPull.run_nil] at actual
      cases actual
      exact ⟨fits, by intros; rfl⟩
  | cons job rest ih =>
      cases projected : projection p h job before with
      | failed fault middle =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before middle fault projected] at actual
          cases actual
      | done value middle =>
          have first := projection_bound job before middle value resource maxDepth maxWidth ready
            (inputs job List.mem_cons_self).1 (inputs job List.mem_cons_self).2 fits
            (depths job List.mem_cons_self) (widths job List.mem_cons_self) projected
          have increase := SourceCurrentConjunctionProjectionResources.jobsBound_ge maxDepth maxWidth
            rest.length (step maxDepth maxWidth resource)
          have current : Effects before middle := by
            simpa only [projected, SourceCurrentConjunctionRowsWorker.Outcome.state] using
              SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job before ready
                (inputs job List.mem_cons_self).1
          cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              rw [SourceCurrentConjunctionRequirementPull.run_step] at actual
              simp only [SourceCurrentConjunctionRequirementPull.step, projected,
                SourceCurrentConjunctionRowsWorker.Outcome.bind,
                tested, ite_true] at actual
              cases actual
              refine ⟨first.1.mono increase, ?_⟩
              intro P H enoughP enoughH
              have replay := first.2 P H enoughP
                (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono increase) enoughH)
              rw [SourceCurrentConjunctionRequirementPull.run_step]
              simp only [SourceCurrentConjunctionRequirementPull.step, replay,
                SourceCurrentConjunctionRowsWorker.Outcome.bind, tested, ite_true]
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before middle value projected tested] at actual
              have tailInputs : ∀ next ∈ rest, Values middle.heap next.1 ∧ ClosedValues next.1 := by
                intro next member
                have old := inputs next (List.mem_cons_of_mem _ member)
                exact ⟨fun node included => current.keeps.available node (old.1 node included), old.2⟩
              have later := ih (collected := collected ++ [value]) (before := middle)
                (resource := step maxDepth maxWidth resource) current.ready tailInputs first.1
                (fun next member => depths next (List.mem_cons_of_mem _ member))
                (fun next member => widths next (List.mem_cons_of_mem _ member)) actual
              refine ⟨later.1, ?_⟩
              intro P H enoughP enoughH
              have replay := first.2 P H enoughP
                (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono increase) enoughH)
              rw [SourceCurrentConjunctionRequirementPull.run_more P H job rest collected before middle value replay tested]
              exact later.2 P H enoughP enoughH

/-- A successful current force fits its explicit job schedule and replays at every larger computed bound. -/
theorem bound {p h handle : Nat} {before after : Cells} {nodes : List Node}
    (actual : force p h handle before = .done nodes after) (resource : Nat)
    (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (fits : Fits resource before.physical.heap) :
    Fits (forecast handle before resource) after.physical.heap ∧
      ∀ P H, projectionFuel handle before ≤ P → readerFuel handle before resource ≤ H →
        force P H handle before = .done nodes after := by
  cases found : lookup handle before with
  | none => simp only [force_step, forceStep, found] at actual; cases actual
  | some cell =>
      cases cell with
      | done original =>
          rw [force_hit p h handle original before found] at actual
          cases actual
          refine ⟨?_, ?_⟩
          · simpa only [forecast, pendingJobs, found, jobsBound, List.length_nil,
              HeightOrderControlled.iterate] using fits
          intro P H _ _
          exact force_hit P H handle _ before found
      | column original =>
          rw [force_step] at actual
          simp only [forceStep, found] at actual
          cases actual
          refine ⟨?_, ?_⟩
          · simpa only [forecast, pendingJobs, found, jobsBound, List.length_nil,
              HeightOrderControlled.iterate, update] using fits
          intro P H _ _
          rw [force_step]
          simp only [forceStep, found]
      | pending cursor =>
          have run := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
          have own := values handle _ found
          have ownClosed := closed handle _ found
          have checked := run_bound cursor.pending cursor.collected before.physical resource
            (depth cursor.pending) (width cursor.pending) ready
            (fun job member => ⟨own.2 job member, ownClosed.2 job member⟩) fits
            (fun job member => maximum_member (fun next => next.2.length) cursor.pending job member)
            (fun job member => maximum_member (fun next => next.1.length) cursor.pending job member) run
          have fitAfter : Fits (forecast handle before resource) after.physical.heap := by
            simpa only [forecast, pendingJobs, found] using checked.1
          refine ⟨fitAfter, ?_⟩
          intro P H enoughP enoughH
          have replay := checked.2 P H
            (by simpa only [projectionFuel, pendingJobs, found] using enoughP)
            (by simpa only [readerFuel, forecast, pendingJobs, found] using enoughH)
          cases observed : force P H handle before with
          | failed diagnostic stopped =>
              obtain ⟨_, _, _, failed, _⟩ :=
                SourceCurrentConjunctionRequirementCellsExecution.force_pending_failed found observed
              rw [replay] at failed
              cases failed
          | done output final =>
              have first := SourceCurrentConjunctionRequirementCellsCompletion.force_done_stable actual
                (Nat.le_max_left p P) (Nat.le_max_left h H)
              have second := SourceCurrentConjunctionRequirementCellsCompletion.force_done_stable observed
                (Nat.le_max_right p P) (Nat.le_max_right h H)
              have same := Outcome.done.inj (first.symm.trans second)
              cases same.1
              cases same.2
              rfl

/-- Current resident closed cells complete at their explicit bounds with the same full endpoint thereafter. -/
theorem complete (handle : Nat) (before : Cells) (resource : Nat)
    (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (fits : Fits resource before.physical.heap) (present : ∃ cell, lookup handle before = some cell) :
    ∃ nodes after,
      (∀ P H, projectionFuel handle before ≤ P → readerFuel handle before resource ≤ H →
        force P H handle before = .done nodes after) ∧
      Fits (forecast handle before resource) after.physical.heap ∧ Effects before.physical after.physical ∧
      SourceCurrentConjunctionRequirementCellsValues.Invariant after ∧
      SourceCurrentConjunctionRequirementCellsClosed.Invariant after ∧
      Values after.physical.heap nodes ∧ ClosedValues nodes := by
  obtain ⟨p, h, nodes, after, actual, kept, finalValues, finalClosed, available, noFree⟩ :=
    SourceCurrentConjunctionRequirementCellsCompletion.force_complete handle before ready values closed present
  have checked := bound (actual p h (Nat.le_refl _) (Nat.le_refl _)) resource ready values closed fits
  exact ⟨nodes, after, checked.2, checked.1, kept, finalValues, finalClosed, available, noFree⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsNumeric

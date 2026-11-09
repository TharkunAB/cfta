import MicroCFTA.SourceCurrentSharedOuterExecutionAncestry
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerGraph
import MicroCFTA.SourceCurrentOuterBusyOwners
import MicroCFTA.SourceCurrentAllocatedSharedPartialActiveFrames

/-!
# Evaluating node owners in actual unfinished outer prefixes

Each transition follows a literal worker branch. A suffix transition retains the literal completed earlier shared call.
Its protected-cell graph is derived from that same return.
Every current evaluating node cell comes from an enclosing activation when
the initial node table is empty. The activation remains evaluating through
its unfinished body prefix. A busy dispatch therefore identifies an exact
key-equal ancestor. This result does not exclude that collision or establish
general outer progress.
-/
namespace MicroCFTA.SourceCurrentSharedOuterActiveAncestry
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentSharedOuterExecutionAncestry
open SourceCurrentAllocatedSharedPartialFrames (Protocol Frame)
open SourceCurrentOuterCopiedWarmHit (Phase)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private theorem erase_failed {actual : Outcome A width}
    (failed : actual.bind (fun _ after => .done () after) = .failed fault after) :
    actual = .failed fault after := by
  cases actual <;> simp_all [Outcome.bind]


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- Run a literal phase with the same lower bounds and erase only its successful value. -/
noncomputable def run (g s r e p h m c n budget : Nat) : Phase width → Outcome Unit width
  | .node fuel request before => (nodeCall fuel g s r e p h m c n budget request before).bind (fun _ after => .done () after)
  | .body fuel request before => (nodeBody fuel g s r e p h m c n budget request before).bind (fun _ after => .done () after)
  | .rows fuel inherited values before => (rows fuel g s r e p h m c n budget inherited values before).bind (fun _ after => .done () after)
  | .descendants fuel inherited edge before => (descendants fuel g s r e p h m c n budget inherited edge before).bind (fun _ after => .done () after)
  | .children fuel combined values before => (children fuel g s r e p h m c n budget combined values before).bind (fun _ after => .done () after)
  | .walk fuel combined index values before => (walk fuel g s r e p h m c n budget combined index values before).bind (fun _ after => .done () after)


private theorem step_frame (step : Step g s r e p h m c n budget first last)
    (valid : Protocol (caller first)) : Frame (caller first) (caller last) := by
  cases step with
  | node_evaluate actual =>
      rename_i request before handle running original fuel
      have frame := SourceCurrentAllocatedSharedPartialFrames.beginNode_frame request before valid
      simpa only [actual, caller] using frame
  | body_rows => exact .refl _ valid
  | rows_edge actual => exact SourceCurrentAllocatedSharedPartialWorkerGraph.edgeCall_frame actual valid
  | rows_tail edgeDone childrenDone =>
      have edge := SourceCurrentAllocatedSharedPartialWorkerGraph.edgeCall_frame edgeDone valid
      exact edge.trans (SourceCurrentAllocatedSharedPartialWorkerGraph.descendants_frame childrenDone edge.valid)
  | descendants_children => exact SourceCurrentAllocatedSharedPartialFrames.advance_frame _ _ _ _ valid
  | children_walk => exact .refl _ valid
  | walk_head => exact SourceCurrentAllocatedSharedPartialFrames.advance_frame _ _ _ _ valid
  | walk_tail actual =>
      have final := SourceCurrentAllocatedSharedPartialWorkerGraph.nodeCall_frame actual ⟨valid.nodes, valid.edges⟩
      exact ⟨final.valid,final.node_keys,final.edge_keys,final.node_running,final.edge_running,
        final.node_returned,final.edge_returned⟩

/-- Every actual prefix derives the protocol of its reached caller. -/
theorem Reached.protocol (actual : Reached g s r e p h m c n budget first last)
    (valid : Protocol (caller first)) : Protocol (caller last) := by
  induction actual with
  | refl => exact valid
  | snoc earlier last ih => exact (step_frame last ih).valid

/-- An enclosing evaluating node owner remains exact throughout an unfinished prefix. -/
theorem Reached.running (actual : Reached g s r e p h m c n budget first last)
    (valid : Protocol (caller first)) (handle : Nat) (owner : NodeRequest)
    (present : (caller first).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    (caller last).nodeResults.cells handle = some ⟨owner, .evaluating⟩ := by
  induction actual with
  | refl => exact present
  | snoc earlier last ih =>
      exact (step_frame last (Reached.protocol earlier valid)).node_running handle owner ih

private theorem step_owner (step : Step g s r e p h m c n budget first last)
    (valid : Protocol (caller first)) (handle : Nat) (owner : NodeRequest)
    (present : (caller last).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    (caller first).nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∨
      ∃ fuel request before running,
        first = .node fuel request before ∧ last = .body fuel owner running ∧
        beginNode request before = (handle, .evaluate owner, running) := by
  cases step with
  | node_evaluate actual =>
      rename_i request before chosen running original fuel
      by_cases same : handle = chosen
      · subst handle
        have own : running.nodeResults.cells chosen = some ⟨original, .evaluating⟩ :=
          (SourceCurrentAllocatedSharedPartialFrames.beginNode_owner request before chosen original running valid actual).1
        have equal : original = owner := by
          have cells := Option.some.inj (own.symm.trans present)
          exact congrArg FlatMemoThunk.Cell.request cells
        subst owner
        exact Or.inr ⟨fuel, request, before, running, rfl, rfl, actual⟩
      · apply Or.inl
        have earlier : (beginNode request before).2.2.nodeResults.cells handle = some ⟨owner, .evaluating⟩ := by
          rw [actual]
          exact present
        have chosenEq : (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1 = chosen :=
          congrArg Prod.fst actual
        exact FlatMemoThunk.lookup_running_before request.key request before.nodeResults handle owner
          (FlatMemoThunk.demand_running_before_other _ handle _ owner (by rw [chosenEq]; exact same) earlier)
  | body_rows => exact Or.inl present
  | rows_edge actual => exact Or.inl ((SourceCurrentAllocatedSharedPartialActiveFrames.edgeCall_done actual).nodes _ _ present)
  | rows_tail edgeDone childrenDone =>
      exact Or.inl (((SourceCurrentAllocatedSharedPartialActiveFrames.edgeCall_done edgeDone).trans
        (SourceCurrentAllocatedSharedPartialActiveFrames.descendants_done childrenDone)).nodes _ _ present)
  | descendants_children => exact Or.inl present
  | children_walk => exact Or.inl present
  | walk_head => exact Or.inl present
  | walk_tail actual => exact Or.inl ((SourceCurrentAllocatedSharedPartialActiveFrames.nodeCall_done actual).nodes _ _ present)

/-- An ancestor retains its exact activation and an unfinished body-to-reader prefix. -/
def Ancestor (g s r e p h m c n budget : Nat) (entryPhase current : Phase width)
    (handle : Nat) (owner : NodeRequest) : Prop :=
  ∃ fuel request before running,
    Reached g s r e p h m c n budget entryPhase (.node fuel request before) ∧
    beginNode request before = (handle, .evaluate owner, running) ∧
    owner.key = request.key ∧ Protocol running ∧
    running.nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∧
    Reached g s r e p h m c n budget (.body fuel owner running) current

private theorem ancestor_extend (ancestor : Ancestor g s r e p h m c n budget entryPhase first handle owner)
    (step : Step g s r e p h m c n budget first last) :
    Ancestor g s r e p h m c n budget entryPhase last handle owner := by
  obtain ⟨fuel,request,before,running,earlier,started,key,valid,present,later⟩ := ancestor
  exact ⟨fuel,request,before,running,earlier,started,key,valid,present,.snoc later step⟩

/-- Every evaluating node cell comes from an enclosing activation when the entry table is idle. -/
theorem Reached.owners (actual : Reached g s r e p h m c n budget entryPhase current)
    (valid : Protocol (caller entryPhase))
    (idle : ∀ handle owner, (caller entryPhase).nodeResults.cells handle ≠ some ⟨owner, .evaluating⟩)
    (handle : Nat) (owner : NodeRequest)
    (present : (caller current).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    Ancestor g s r e p h m c n budget entryPhase current handle owner := by
  induction actual with
  | refl => exact False.elim (idle handle owner present)
  | snoc earlier last ih =>
      rcases step_owner last (Reached.protocol earlier valid) handle owner present with old | fresh
      · exact ancestor_extend (ih old) last
      · obtain ⟨fuel,request,before,running,firstEq,lastEq,started⟩ := fresh
        cases firstEq
        cases lastEq
        have protocol := Reached.protocol earlier valid
        have owned := SourceCurrentAllocatedSharedPartialFrames.beginNode_owner request before handle owner running protocol started
        have runningValid := SourceCurrentAllocatedSharedPartialFrames.beginNode_frame request before protocol
        rw [started] at runningValid
        exact ⟨fuel,request,before,running,earlier,started,owned.2,runningValid.valid,owned.1,.refl _⟩

/-- Initial outer tables derive all current owner ancestry without a supplied stack invariant. -/
theorem initial_owners (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (fuel : Nat) (request : NodeRequest)
    (actual : Reached g s r e p h m c n budget (.node fuel request (initial checked merge fourth)) current)
    (handle : Nat) (owner : NodeRequest)
    (present : (caller current).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    Ancestor g s r e p h m c n budget (.node fuel request (initial checked merge fourth)) current handle owner :=
  Reached.owners actual (SourceCurrentAllocatedSharedPartialFrames.initial_protocol checked merge fourth)
    (fun _ _ impossible => by cases impossible) handle owner present

/-- An actual busy dispatch identifies a key-equal enclosing activation, not a completed sibling. -/
theorem busy (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (fuel : Nat) (request : NodeRequest)
    (actual : Reached g s r e p h m c n budget (.node fuel request (initial checked merge fourth))
      (.node next candidate before))
    (observed : beginNode candidate before = (handle, .busy, after)) :
    after = before ∧ ∃ owner,
      before.nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∧ owner.key = candidate.key ∧
      Ancestor g s r e p h m c n budget (.node fuel request (initial checked merge fourth))
        (.node next candidate before) handle owner := by
  obtain ⟨rfl,linked,owner,present⟩ := SourceCurrentOuterBusyOwners.node_busy candidate before after handle observed
  have protocol := Reached.protocol actual (SourceCurrentAllocatedSharedPartialFrames.initial_protocol checked merge fourth)
  obtain ⟨cell,found,key⟩ := protocol.nodes.linked candidate.key handle linked
  have same := Option.some.inj (found.symm.trans present)
  subst cell
  exact ⟨rfl,owner,present,key,initial_owners checked merge fourth fuel request actual handle owner present⟩

/-- A reached failure propagates through each actual prefix with the same full caller. -/
theorem Step.failed (actual : Step g s r e p h m c n budget first last)
    (failed : run g s r e p h m c n budget last = .failed fault after) :
    run g s r e p h m c n budget first = .failed fault after := by
  cases actual with
  | node_evaluate actual =>
      have actualFailed := erase_failed failed
      simp only [run, nodeCall, actual, actualFailed, Outcome.bind]
  | body_rows actual =>
      have actualFailed := erase_failed failed
      simp only [run, nodeBody, actual, actualFailed, Outcome.bind]
  | rows_edge actual =>
      have actualFailed := erase_failed failed
      simp only [run, rows, actual, actualFailed, Outcome.bind]
  | rows_tail edge children =>
      have actualFailed := erase_failed failed
      simp only [run, rows, edge, children, actualFailed, Outcome.bind]
  | descendants_children actual =>
      have actualFailed := erase_failed failed
      simp only [SourceCurrentAllocatedSharedPartialGraph.prefixState,
        SourceCurrentAllocatedInheritedPrefix.state] at actualFailed
      simp only [run, descendants, actual, actualFailed, Outcome.bind]
  | children_walk live =>
      rename_i combined fuel values before
      simp only [run] at failed ⊢
      cases combined with
      | contradiction => exact False.elim (live rfl)
      | live identity records => simpa only [children] using failed
  | walk_head =>
      have actualFailed := erase_failed failed
      simp only [run, walk, actualFailed, Outcome.bind]
  | walk_tail actual =>
      have actualFailed := erase_failed failed
      simp only [run, walk, actual, actualFailed, Outcome.bind]

/-- Literal failure correspondence holds for the entire derived unfinished prefix. -/
theorem Reached.failed (actual : Reached g s r e p h m c n budget first last)
    (failed : run g s r e p h m c n budget last = .failed fault after) :
    run g s r e p h m c n budget first = .failed fault after := by
  induction actual with
  | refl => exact failed
  | snoc earlier last ih => exact ih (Step.failed last failed)

end MicroCFTA.SourceCurrentSharedOuterActiveAncestry

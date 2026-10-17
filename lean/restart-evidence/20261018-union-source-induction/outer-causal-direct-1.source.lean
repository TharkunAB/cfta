import MicroCFTA.SourceCurrentOuterCopiedWarmHit
import MicroCFTA.SourceCurrentOuterBusyOwners
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames

/-!
# Evaluating node owners in actual unfinished outer prefixes

Each transition follows a literal worker branch. A suffix transition also
retains the actual completed earlier graph and its literal worker equation.
Every current evaluating node cell comes from an enclosing activation when
the initial node table is empty. The activation remains evaluating through
its unfinished body prefix. A busy dispatch therefore identifies an exact
key-equal ancestor. This result does not exclude that collision or establish
general outer progress.
-/
namespace MicroCFTA.SourceCurrentOuterActiveAncestry
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialFrames (Protocol Frame)
open SourceCurrentOuterCopiedWarmHit (Phase)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- Read the exact full caller at a literal phase entry. -/
def caller : Phase width → Caller width
  | .node _ _ before | .body _ _ before | .rows _ _ _ before |
    .descendants _ _ _ before | .children _ _ _ before | .walk _ _ _ _ before => before

/-- A prefix enters a literal branch or skips only completed earlier calls. -/
inductive Step (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- A node enters its exact stored owner after demand. -/
  | node_evaluate (actual : beginNode request before = (handle, .evaluate original, running)) :
      Step g s r e p h m c n budget (.node fuel request before) (.body fuel original running)
  /-- An ordinary body enters its original rows. -/
  | body_rows (actual : request.value = .node entry originals depth free) :
      Step g s r e p h m c n budget (.body (fuel + 1) request before)
        (.rows fuel request.inherited originals before)
  /-- A completed parent edge precedes its actual descendants. -/
  | rows_edge
      (actual : edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
      (graph : SourceCurrentAllocatedPartialGraph.EdgeCall budget ⟨inherited, original⟩ before narrowed middle) :
      Step g s r e p h m c n budget (.rows (fuel + 1) inherited (original :: rest) before)
        (.descendants fuel inherited narrowed middle)
  /-- The row suffix starts after the exact completed parent and descendants. -/
  | rows_tail
      (edge : edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
      (edgeGraph : SourceCurrentAllocatedPartialGraph.EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
      (children : descendants fuel g s r e p h m c n budget inherited narrowed middle = .done result after)
      (childrenGraph : SourceCurrentAllocatedPartialGraph.Descendants budget inherited narrowed middle result after) :
      Step g s r e p h m c n budget (.rows (fuel + 1) inherited (original :: rest) before)
        (.rows fuel inherited rest after)
  /-- The inherited prefix enters the exact returned children. -/
  | descendants_children {edge : Edge}
      (actual : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited
        before.checked.operations).1 = .ok (some combined)) :
      Step g s r e p h m c n budget (.descendants fuel inherited edge before)
        (.children fuel combined edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited))
  /-- A live combined payload enters its indexed walk. -/
  | children_walk (live : combined ≠ .contradiction) :
      Step g s r e p h m c n budget (.children fuel combined values before) (.walk fuel combined 0 values before)
  /-- The next node uses the actual indexed descent. -/
  | walk_head :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
          (SourceCurrentAllocatedPartialGraph.descend before combined index).2)
  /-- The next slot starts after the actual completed earlier node. -/
  | walk_tail
      (actual : nodeCall fuel g s r e p h m c n budget
        ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
        (SourceCurrentAllocatedPartialGraph.descend before combined index).2 = .done result middle)
      (graph : SourceCurrentAllocatedPartialGraph.NodeCall budget
        ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
        (SourceCurrentAllocatedPartialGraph.descend before combined index).2 result middle) :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.walk fuel combined (index + 1) rest middle)

/-- A finite literal prefix retains every completed earlier-call witness. -/
inductive Reached (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- The entry phase is already reached. -/
  | refl (phase) : Reached g s r e p h m c n budget phase phase
  /-- An actual branch extends the preceding prefix. -/
  | snoc (earlier : Reached g s r e p h m c n budget first middle)
      (last : Step g s r e p h m c n budget middle final) :
      Reached g s r e p h m c n budget first final

/-- Consecutive actual prefixes form one prefix. -/
theorem Reached.trans (first : Reached g s r e p h m c n budget initial middle)
    (last : Reached g s r e p h m c n budget middle final) :
    Reached g s r e p h m c n budget initial final := by
  induction last with
  | refl => exact first
  | snoc earlier last ih => exact .snoc ih last

private theorem step_frame (step : Step g s r e p h m c n budget first last)
    (valid : Protocol (caller first)) : Frame (caller first) (caller last) := by
  cases step with
  | node_evaluate actual =>
      have frame := SourceCurrentAllocatedPartialFrames.beginNode_frame _ _ valid
      simpa only [actual, caller] using frame
  | body_rows => exact .refl _ valid
  | rows_edge _ graph => exact SourceCurrentAllocatedPartialFrames.edge_call graph valid
  | rows_tail _ edgeGraph _ childrenGraph =>
      have edge := SourceCurrentAllocatedPartialFrames.edge_call edgeGraph valid
      exact edge.trans (SourceCurrentAllocatedPartialFrames.descendants childrenGraph edge.valid)
  | descendants_children => exact SourceCurrentAllocatedPartialFrames.advance_frame _ _ _ _ valid
  | children_walk => exact .refl _ valid
  | walk_head => exact SourceCurrentAllocatedPartialFrames.advance_frame _ _ _ _ valid
  | walk_tail _ graph =>
      have first := SourceCurrentAllocatedPartialFrames.advance_frame _ _ _ _ valid
      exact first.trans (SourceCurrentAllocatedPartialFrames.node_call graph first.valid)

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
      exact (step_frame last (earlier.protocol valid)).node_running handle owner ih

private theorem step_owner (step : Step g s r e p h m c n budget first last)
    (handle : Nat) (owner : NodeRequest)
    (present : (caller last).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    (caller first).nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∨
      ∃ fuel request before running,
        first = .node fuel request before ∧ last = .body fuel owner running ∧
        beginNode request before = (handle, .evaluate owner, running) := by
  cases step with
  | node_evaluate actual =>
      rename_i request before chosen original running fuel
      by_cases same : handle = chosen
      · subst handle
        have own : running.nodeResults.cells chosen = some ⟨original, .evaluating⟩ := by
          let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
          have evaluated := FlatMemoThunk.demand_evaluate published.1 published.2 _ original
            (Prod.ext (congrArg (fun result => result.2.1) actual) rfl)
          simpa only [← actual] using evaluated.2
        have equal : original = owner := by
          have cells := Option.some.inj (own.symm.trans present)
          exact congrArg FlatMemoThunk.Cell.request cells
        subst owner
        exact Or.inr ⟨fuel, request, before, running, rfl, rfl, actual⟩
      · apply Or.inl
        exact FlatMemoThunk.lookup_running_before request.key request before.nodeResults handle owner
          (FlatMemoThunk.demand_running_before_other _ handle _ owner
            (by simpa only [actual] using same) (by simpa only [actual] using present))
  | body_rows => exact Or.inl present
  | rows_edge _ graph => exact Or.inl ((SourceCurrentAllocatedPartialActiveFrames.edge_call graph).nodes _ _ present)
  | rows_tail _ edgeGraph _ childrenGraph =>
      exact Or.inl (((SourceCurrentAllocatedPartialActiveFrames.edge_call edgeGraph).trans
        (SourceCurrentAllocatedPartialActiveFrames.descendants childrenGraph)).nodes _ _ present)
  | descendants_children => exact Or.inl present
  | children_walk => exact Or.inl present
  | walk_head => exact Or.inl present
  | walk_tail _ graph => exact Or.inl ((SourceCurrentAllocatedPartialActiveFrames.node_call graph).nodes _ _ present)

/-- An ancestor retains its exact activation and an unfinished body-to-reader prefix. -/
def Ancestor (g s r e p h m c n budget : Nat) (initial current : Phase width)
    (handle : Nat) (owner : NodeRequest) : Prop :=
  ∃ fuel request before running,
    Reached g s r e p h m c n budget initial (.node fuel request before) ∧
    beginNode request before = (handle, .evaluate owner, running) ∧
    owner.key = request.key ∧ Protocol running ∧
    running.nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∧
    Reached g s r e p h m c n budget (.body fuel owner running) current

private theorem ancestor_extend (ancestor : Ancestor g s r e p h m c n budget initial first handle owner)
    (step : Step g s r e p h m c n budget first last) :
    Ancestor g s r e p h m c n budget initial last handle owner := by
  obtain ⟨fuel,request,before,running,earlier,started,key,valid,present,later⟩ := ancestor
  exact ⟨fuel,request,before,running,earlier,started,key,valid,present,.snoc later step⟩

/-- Every evaluating node cell comes from an enclosing activation when the entry table is idle. -/
theorem Reached.owners (actual : Reached g s r e p h m c n budget initial current)
    (valid : Protocol (caller initial))
    (idle : ∀ handle owner, (caller initial).nodeResults.cells handle ≠ some ⟨owner, .evaluating⟩)
    (handle : Nat) (owner : NodeRequest)
    (present : (caller current).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    Ancestor g s r e p h m c n budget initial current handle owner := by
  induction actual with
  | refl => exact False.elim (idle handle owner present)
  | snoc earlier last ih =>
      rcases step_owner last handle owner present with old | fresh
      · exact ancestor_extend (ih old) last
      · obtain ⟨fuel,request,before,running,first,last,started⟩ := fresh
        subst first
        subst last
        have protocol := earlier.protocol valid
        have owned := SourceCurrentAllocatedPartialFrames.beginNode_owner request before handle owner running protocol started
        have runningValid := SourceCurrentAllocatedPartialFrames.beginNode_frame request before protocol
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
  actual.owners (SourceCurrentAllocatedPartialFrames.initial_protocol checked merge fourth)
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
  have protocol := actual.protocol (SourceCurrentAllocatedPartialFrames.initial_protocol checked merge fourth)
  obtain ⟨cell,found,key⟩ := protocol.nodes.linked candidate.key handle linked
  have same := Option.some.inj (found.symm.trans present)
  subst cell
  exact ⟨rfl,owner,present,key,initial_owners checked merge fourth fuel request actual handle owner present⟩

/-- A reached failure propagates through each actual prefix with the same full caller. -/
theorem Step.failed (actual : Step g s r e p h m c n budget first last)
    (failed : last.run g s r e p h m c n budget = .failed fault after) :
    first.run g s r e p h m c n budget = .failed fault after := by
  cases actual with
  | node_evaluate actual => exact SourceCurrentOuterCopiedWarmHit.Step.failed (.node_evaluate actual) failed
  | body_rows actual => exact SourceCurrentOuterCopiedWarmHit.Step.failed (.body_rows actual) failed
  | rows_edge actual _ => exact SourceCurrentOuterCopiedWarmHit.Step.failed (.rows_edge actual) failed
  | rows_tail edge _ children _ =>
      have suffix : rows _ g s r e p h m c n budget _ _ _ = .failed fault after := by
        cases outcome : rows _ g s r e p h m c n budget _ _ _ <;>
          simp_all only [Phase.run, Outcome.bind]
      simp only [Phase.run, rows, edge, children, suffix, Outcome.bind]
  | descendants_children actual => exact SourceCurrentOuterCopiedWarmHit.Step.failed (.descendants_children actual) failed
  | children_walk actual => exact SourceCurrentOuterCopiedWarmHit.Step.failed (.children_walk actual) failed
  | walk_head => exact SourceCurrentOuterCopiedWarmHit.Step.failed .walk_head failed
  | walk_tail actual _ => exact SourceCurrentOuterCopiedWarmHit.Step.failed (.walk_tail actual) failed

/-- Literal failure correspondence holds for the entire derived unfinished prefix. -/
theorem Reached.failed (actual : Reached g s r e p h m c n budget first last)
    (failed : last.run g s r e p h m c n budget = .failed fault after) :
    first.run g s r e p h m c n budget = .failed fault after := by
  induction actual with
  | refl => exact failed
  | snoc earlier last ih => exact ih (last.failed failed)

end MicroCFTA.SourceCurrentOuterActiveAncestry

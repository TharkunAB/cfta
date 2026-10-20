import MicroCFTA.SourceCurrentOuterRowFieldOrigins
import MicroCFTA.SourceCurrentActualParentRowOrigins
import MicroCFTA.SourceCurrentAllocatedLocalPlain
import MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain

/-!
# Plain row shapes through actual outer prefixes

A Parent call with empty effective own equalities retains its original
children, erases their slots, or returns the Empty sentinel. Returned edge
cells retain this conditional fact for their actual captured request.
Cold calls and warm hits derive it from physical entry facts. Completed
workers and unfinished prefixes preserve it without a future return.
-/
namespace MicroCFTA.SourceCurrentOuterPlainRowShapes
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "NativeGood" => SourceCurrentNativeOperationHeap.Good
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable {width : Nat}

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → SourceCurrentEmptinessMemo.Memo →
      SourceCurrentMemoMergeGraph.Memo Symbol Guard → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : SourceCurrentEmptinessMemo.Memo}
    {saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧
      next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

section ParentExecution
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem parent
    {g s r e p h m c n budget symbol original inherited children before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children
      before fourth memo = .done result after saved current)
    (good : NativeGood (before : Checked width))
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧
      Values before.native.machine.heap children)
    (plain : SourceCompactGuards.sourceEqualities original = some []) :
    result.children = children ∨ result.children = EqualityLeafProjectionRuntimeEmpty.erase children ∨
      result.children = [.empty] := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    exact Or.inr (Or.inr (SourceCurrentActualParentRowOrigins.reject_children symbol before good))
  | false =>
    obtain ⟨field,inheritedReady,available⟩ := live rejected
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,Bool.false_eq_true,ite_false] at actual
    cases loaded : SourceEqualityConstraintFieldLookup.load original before.operations.constraints with
    | error => simp only [loaded] at actual; cases actual
    | ok value =>
      cases value with
      | none => simp only [loaded] at actual; cases actual
      | some loadedValue =>
        simp only [loaded] at actual
        obtain ⟨values,middle,completed,warm,first,last⟩ := parent_bind_done _ _ actual
        have properties := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
          good.operations.constraints field.1 loadedValue loaded
        have reduced : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
            loadedValue inherited children before fourth memo = .done values middle completed warm := by
          cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
              loadedValue inherited children before fourth memo with
          | failed => simp only [SourceCurrentAllocatedParentWorker.reduceChildren,observed] at first; cases first
          | done output checked next current =>
            simp only [SourceCurrentAllocatedParentWorker.reduceChildren,observed] at first
            cases first
            rfl
        have ownEmpty := SourceCurrentAllocatedLocalPlain.of_readback properties.2 plain
        have localShape := (SourceCurrentAllocatedLocalPlain.done_shape g s r e p h m c n budget
          loadedValue inherited children before middle fourth completed memo warm values
          good.operations properties.1 inheritedReady ownEmpty reduced).2.2.2
        obtain ⟨effect,_retained,known⟩ := SourceCurrentParentOperationInvariants.reduce reduced good stored
          properties.1 inheritedReady available
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk returned checked =>
          cases returned with
          | error => simp only [SourceCurrentAllocatedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedParentWorker.build,observed] at last
            cases last
            have actualChildren := SourceCurrentActualParentRowOrigins.build_children observed effect.good
              (properties.1.grows effect.operations.constraint_growth) known
            cases accepted : SourceEqualityMkEdgeAllocation.accepted
                (SourceEqualityConjoinAllocation.readback loadedValue) values.length with
            | false => exact Or.inr (Or.inr (by simpa only [accepted,Bool.false_eq_true,ite_false] using actualChildren))
            | true =>
              have sameChildren : result.children = values := by
                simpa only [accepted,ite_true] using actualChildren
              rcases localShape with same | erased
              · exact Or.inl (sameChildren.trans same)
              · exact Or.inr (Or.inl (sameChildren.trans erased))

end ParentExecution

/-- A returned edge retains its plain child shape at the same captured request. -/
def Origins (before : Caller width) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key)
    (fun cell : FlatMemoThunk.Cell EdgeRequest Edge =>
      ∀ result, cell.status = .returned result →
        SourceCompactGuards.sourceEqualities cell.request.value.entry.key.constraint = some [] →
          Shape cell.request.value result)
    before.edgeResults

/-- Initially empty edge tables require no returned-row premise. -/
theorem initial (checked : Checked width) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (fourth : SourceCurrentEmptinessMemo.Memo) : Origins (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  FlatMemoThunk.empty_valid _ _

private theorem demand_valid (handle : Nat) (state : FlatMemoThunk.State Key Request Result)
    (keyOf : Request → Key → Prop) (property : FlatMemoThunk.Cell Request Result → Prop)
    (valid : FlatMemoThunk.Valid keyOf property state)
    (started : ∀ request, property ⟨request,.suspended⟩ → property ⟨request,.evaluating⟩) :
    FlatMemoThunk.Valid keyOf property (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand,found] using valid
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | evaluating | returned value => simpa only [FlatMemoThunk.demand,found] using valid
      | suspended =>
        simp only [FlatMemoThunk.demand,found]
        exact FlatMemoThunk.setStatus_valid _ _ _ _ _ valid _ found (started request (valid.checked _ _ found))

private theorem begin_origins (request : EdgeRequest) {before : Caller width} (origins : Origins before) :
    Origins (beginEdge request before).2.2 := by
  apply demand_valid
  · exact FlatMemoThunk.lookup_valid _ _ _ _ _ origins rfl (by intro result impossible; cases impossible)
  · intro owner _ result impossible
    cases impossible

private theorem begin_good (request : EdgeRequest) {before : Caller width}
    (good : Good before) (ready : EdgeReady before request) : Good (beginEdge request before).2.2 := by
  refine ⟨good.checked,good.stored,good.probes,good.nodes,?_⟩
  apply demand_valid
  · exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.edges rfl
      ⟨ready,by intro value impossible; cases impossible⟩
  · intro owner supported
    exact ⟨supported.1,by intro value impossible; cases impossible⟩

private theorem demand_table (handle : Nat) (state : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle state).2.table = state.table := by
  cases found : state.cells handle with
  | none => simp only [FlatMemoThunk.demand,found]
  | some cell => cases phase : cell.status <;> simp only [FlatMemoThunk.demand,found,phase,FlatMemoThunk.setStatus]

private theorem begin_key (request : EdgeRequest) (before : Caller width) :
    (beginEdge request before).2.2.edgeResults.table request.key = some (beginEdge request before).1 := by
  change (FlatMemoThunk.demand _ _).2.table _ = _
  rw [demand_table]
  exact FlatMemoThunk.lookup_stored _ _ _

private theorem edge_same_key {before : Caller width} {first second : EdgeRequest}
    (good : Good before) (left : EdgeReady before first) (right : EdgeReady before second)
    (same : first.key = second.key) : first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _ good.checked.operations.constraints
    first.inherited second.inherited left.1 right.1 (congrArg Prod.fst same)
  have values := edge_identity_unique _ good.checked.heap.semantic.1.normal.facts.coherent
    first.value second.value left.2 right.2 (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

private theorem begin_request {before running : Caller width} {request owner : EdgeRequest}
    {handle : Nat} {status : FlatMemoThunk.Status Edge}
    (good : Good running) (ready : EdgeReady before request)
    (began : beginEdge request before = (handle,action,running))
    (found : running.edgeResults.cells handle = some ⟨owner,status⟩) : owner = request := by
  have same := (beginEdge_components request before).1
  rw [began] at same
  have candidate : EdgeReady running request := by
    unfold EdgeReady
    rw [same]
    exact ready
  have stored := begin_key request before
  rw [began] at stored
  obtain ⟨cell,present,linked⟩ := good.edges.linked request.key handle stored
  have cells := Option.some.inj (present.symm.trans found)
  subst cell
  exact edge_same_key good (good.edges.checked _ _ found).1 candidate linked

private theorem finish_origins (handle : Nat) (owner : EdgeRequest) (value : Edge) {before : Caller width}
    (origins : Origins before) (found : before.edgeResults.cells handle = some ⟨owner,.evaluating⟩)
    (fields : SourceCompactGuards.sourceEqualities owner.value.entry.key.constraint = some [] →
      Shape owner.value value) :
    Origins (finishEdge handle value before) := by
  simp only [Origins,finishEdge,FlatMemoThunk.finish,found]
  apply FlatMemoThunk.setStatus_valid _ _ _ _ _ origins _ found
  intro result same
  cases FlatMemoThunk.Status.returned.inj same
  exact fields

private theorem bind_done (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

section OuterExecution
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem edge_body {fuel g s r e p h m c n budget request before value after}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request) (origins : Origins before) :
    Origins after ∧ after.edgeResults = before.edgeResults ∧
      (SourceCompactGuards.sourceEqualities request.value.entry.key.constraint = some [] → Shape request.value value) := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody,observed] at actual; cases actual
  | done result checked fourth memo =>
    simp only [edgeBody,observed] at actual
    cases actual
    exact ⟨origins,rfl,fun plain => parent observed good.checked good.stored
      (fun _ => ⟨good.checked.fields request.value.entry.key request.value ready.2,ready.1,
        good.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ ready.2⟩) plain⟩

/-- Actual cold and warm calls derive the conditional shape at their same captured request. -/
theorem edge_call {fuel g s r e p h m c n budget request before value after}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request) (origins : Origins before) :
    Origins after ∧ (SourceCompactGuards.sourceEqualities request.value.entry.key.constraint = some [] → Shape request.value value) := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have initial := begin_good request good ready
  have prior := begin_origins request origins
  rw [started] at initial prior
  cases action with
  | busy | absent => simp only [edgeCall,started] at actual; cases actual
  | ready result =>
    simp only [edgeCall,started] at actual
    cases actual
    let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
    have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
    change FlatMemoThunk.demand published.1 published.2 = (.ready value,after.edgeResults) at observed
    obtain ⟨owner,found,same⟩ := FlatMemoThunk.demand_ready_original _ _ value _ observed
    rw [← same] at found
    have handles : published.1 = handle := congrArg Prod.fst started
    rw [handles] at found
    have ownerEq := begin_request initial ready started found
    exact ⟨prior,ownerEq ▸ prior.checked _ _ found value rfl⟩
  | evaluate owner =>
    let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
    have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
    change FlatMemoThunk.demand published.1 published.2 = (.evaluate owner,running.edgeResults) at observed
    have found := (FlatMemoThunk.demand_evaluate _ _ _ owner observed).2
    have handles : published.1 = handle := congrArg Prod.fst started
    rw [handles] at found
    have ownerEq := begin_request initial ready started found
    obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [edgeCall,started] using actual)
    cases finished
    obtain ⟨final,same,fields⟩ := edge_body body initial (initial.edges.checked _ _ found).1 prior
    have retained : middle.edgeResults.cells handle = some ⟨owner,.evaluating⟩ := same ▸ found
    exact ⟨finish_origins handle owner value final retained fields,ownerEq ▸ fields⟩

open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

private theorem step_inputs (step : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) : Good (caller last) ∧ Inputs last :=
  SourceCurrentOuterPrefixInvariants.reached (.snoc (.refl _) step) good inputs

private def NodeAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeCall fuel g s r e p h m c n budget request before = .done value after →
  Good (width := width) before → NodeReady before request → Origins before → Origins after
private def BodyAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeBody fuel g s r e p h m c n budget request before = .done value after →
  Good (width := width) before → NodeReady before request → Origins before → Origins after
private def RowsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  rows fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
  Origins before → Origins after
private def DescendantsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited value before result after},
  descendants fuel g s r e p h m c n budget inherited value before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → EdgeResident before.checked.native.machine.heap value →
  Origins before → Origins after
private def ChildrenAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  children fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
  Origins before → Origins after
private def WalkAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited index values before result after},
  walk fuel g s r e p h m c n budget inherited index values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
  Origins before → Origins after

private theorem all_done (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited index values before result after actual good ready available origins
      cases values with
      | nil => simp only [walk] at actual; cases actual; exact origins
      | cons value values =>
        cases fuel with
        | zero => simp only [walk] at actual; cases actual
        | succ fuel =>
          obtain ⟨head,middle,first,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
          have child := step_inputs (Step.walk_head (fuel := fuel) (value := value) (rest := values)
            (combined := inherited) (index := index) (before := before)
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)) good ⟨ready,available⟩
          have current := (ih fuel (Nat.lt_succ_self _)).1 first child.1 child.2 origins
          obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
          cases last
          have remaining := step_inputs (Step.walk_tail first) good ⟨ready,available⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 rest remaining.1 remaining.2.1 remaining.2.2 current
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready available origins
      cases inherited with
      | contradiction =>
        simp only [SourceCurrentAllocatedPartialWorker.children] at actual
        cases actual
        exact origins
      | live identity records => exact walkAt (by simpa only [SourceCurrentAllocatedPartialWorker.children] using actual) good ready available origins
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before result after actual good ready resident origins
      obtain ⟨combined,prefixDone,_,_,_,_⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
        value.entry.key.constraint inherited before.checked.operations good.checked.operations ready
        (good.checked.fields value.entry.key value resident)
      obtain ⟨values,middle,first,last⟩ := bind_done _ _
        (by simpa only [descendants,prefixDone] using actual)
      have start := step_inputs (Step.descendants_children (fuel := fuel) prefixDone
        (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)) good ⟨ready,resident⟩
      have current := childrenAt first start.1 start.2.1 start.2.2 origins
      cases last
      exact current
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready resident origins
      cases values with
      | nil => simp only [rows] at actual; cases actual; exact origins
      | cons value values =>
        cases fuel with
        | zero => simp only [rows] at actual; cases actual
        | succ fuel =>
          obtain ⟨narrowed,middle,first,later⟩ := bind_done _ _ (by simpa only [rows] using actual)
          have current := (edge_call first good ⟨ready,resident _ List.mem_cons_self⟩ origins).1
          obtain ⟨head,afterChildren,childrenDone,last⟩ := bind_done _ _ later
          have child := step_inputs (Step.rows_edge (rest := values) first) good ⟨ready,resident⟩
          have next := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 childrenDone child.1 child.2.1 child.2.2 current
          obtain ⟨tail,final,rest,done⟩ := bind_done _ _ last
          cases done
          have remaining := step_inputs (Step.rows_tail first childrenDone) good ⟨ready,resident⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.1 rest remaining.1 remaining.2.1 remaining.2.2 next
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready origins
      cases request with
      | mk inherited original =>
        cases original with
        | empty | union => simp only [nodeBody] at actual; cases actual; exact origins
        | reference name => simp only [nodeBody] at actual; cases actual
        | mu entry body depth ordinary =>
          have built := SourceCurrentMuReconstructionEffects.node_body fuel g s r e p h m c n budget
            entry body depth ordinary inherited before good.checked good.probes ready.2
          rw [built] at actual
          cases actual
          exact origins
        | node entry originals depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
            obtain ⟨rebuilt,middle,first,last⟩ := bind_done _ _ (by simpa only [nodeBody] using actual)
            have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ ready.2.resident
            have current := (ih fuel (Nat.lt_succ_self _)).2.2.1 first good ready.1 resident origins
            cases last
            exact current
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready origins
      rcases started : beginNode request before with ⟨handle,action,running⟩
      have unchanged : (beginNode request before).2.2.edgeResults = before.edgeResults := rfl
      rw [started] at unchanged
      have prior : Origins running := by change FlatMemoThunk.Valid _ _ running.edgeResults; rw [unchanged]; exact origins
      cases action with
      | busy | absent => simp only [nodeCall,started] at actual; cases actual
      | ready result => simp only [nodeCall,started] at actual; cases actual; exact prior
      | evaluate original =>
        obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [nodeCall,started] using actual)
        have current := SourceCurrentOuterPrefixInvariants.activate started good ready
        have final := bodyAt body current.1 current.2 prior
        cases finished
        exact final
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

private theorem node_done {fuel g s r e p h m c n budget request before value after}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : NodeReady before request) (origins : Origins before) :
    Origins after := (all_done fuel).1 actual good ready origins

private theorem step_origins (actual : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (origins : Origins (caller first)) :
    Origins (caller last) := by
  cases actual with
  | node_evaluate started =>
    have same := congrArg (fun result => result.2.2.edgeResults) started
    unfold Origins at *
    dsimp only [Prod.snd] at same
    dsimp only [SourceCurrentOuterActiveAncestry.caller] at origins ⊢
    rw [← same]
    exact origins
  | body_rows => exact origins
  | rows_edge actual => exact (edge_call actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins).1
  | rows_tail edge children =>
    have current := (edge_call edge good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins).1
    have child := step_inputs (Step.rows_edge edge) good inputs
    exact (all_done _).2.2.2.1 children child.1 child.2.1 child.2.2 current
  | descendants_children | children_walk | walk_head => exact origins
  | walk_tail actual =>
    have child := step_inputs (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) Step.walk_head good inputs
    exact node_done actual child.1 child.2 origins

/-- Actual unfinished prefixes preserve plain shapes from their initial edge cells. -/
theorem reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (origins : Origins (caller first)) :
    Origins (caller last) := by
  induction actual with
  | refl => exact origins
  | snoc earlier last ih =>
    have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
    exact step_origins last current.1 current.2 ih

end OuterExecution

end MicroCFTA.SourceCurrentOuterPlainRowShapes

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentOuterPlainRowShapes.Origins
#print MicroCFTA.SourceCurrentOuterPlainRowShapes.Origins
#print axioms MicroCFTA.SourceCurrentOuterPlainRowShapes.Origins
#check @MicroCFTA.SourceCurrentOuterPlainRowShapes.initial
#print MicroCFTA.SourceCurrentOuterPlainRowShapes.initial
#print axioms MicroCFTA.SourceCurrentOuterPlainRowShapes.initial
#check @MicroCFTA.SourceCurrentOuterPlainRowShapes.edge_call
#print MicroCFTA.SourceCurrentOuterPlainRowShapes.edge_call
#print axioms MicroCFTA.SourceCurrentOuterPlainRowShapes.edge_call
#check @MicroCFTA.SourceCurrentOuterPlainRowShapes.reached
#print MicroCFTA.SourceCurrentOuterPlainRowShapes.reached
#print axioms MicroCFTA.SourceCurrentOuterPlainRowShapes.reached

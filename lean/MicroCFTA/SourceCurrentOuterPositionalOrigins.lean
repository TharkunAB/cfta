import MicroCFTA.SourceCurrentActualParentRowOrigins
import MicroCFTA.SourceCurrentOuterGuardHeapReturns

/-!
# Indexed row origins through actual outer result cells

Cold Parent calls derive the positional row relation from initial facts.
Their actual returned edge cells retain that relation for warm requests.
Successful calls and unfinished prefixes produce the memo invariant from
initial tables. Source footprints and successful call equations remain
explicit. No future completion or row-origin law is supplied.
-/
namespace MicroCFTA.SourceCurrentOuterPositionalOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants
open SourceCurrentActualRequiredRowOrigins (Link)
open SourceCurrentClassPositionalFootprints (Unselected)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
variable {width : Nat}

/-- Every untouched continuation of a present returned child retains its indexed source row. -/
def EdgeLink (original result : Edge) : Prop :=
  ∀ index childIndex,
    (∀ originals : List Record,
      SourceEqualityPhysicalPayload.own original.entry.key.constraint = .ok (some originals) →
        ∀ record ∈ originals, Unselected record index childIndex) →
    ∀ source output : Node, original.children[index]? = some source →
      result.children[index]? = some output → Link childIndex source output

/-- Returned outer edge cells retain the positional relation of their exact captured request. -/
def Origins (before : Caller width) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key)
    (fun cell : FlatMemoThunk.Cell EdgeRequest Edge =>
      ∀ result, cell.status = .returned result → EdgeLink cell.request.value result)
    before.edgeResults

/-- Empty outer result tables require no earlier result-origin premise. -/
theorem initial (checked : Checked width) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (fourth : SourceCurrentEmptinessMemo.Memo) :
    Origins (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
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
    (link : EdgeLink owner.value value) :
    Origins (finishEdge handle value before) := by
  simp only [Origins,finishEdge,FlatMemoThunk.finish,found]
  apply FlatMemoThunk.setStatus_valid _ _ _ _ _ origins _ found
  intro result same
  cases FlatMemoThunk.Status.returned.inj same
  exact link

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
    (good : Good (width := width) before) (ready : EdgeReady before request)
    (guards : GuardHeap before.checked.native.machine.heap) (origins : Origins before) :
    Origins after ∧ after.edgeResults = before.edgeResults ∧ EdgeLink request.value value := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody,observed] at actual; cases actual
  | done result checked fourth memo =>
    simp only [edgeBody,observed] at actual
    cases actual
    refine ⟨origins,rfl,?_⟩
    intro index childIndex footprint source output input returned
    exact SourceCurrentActualParentRowOrigins.edge observed good.checked good.stored
      (fun _ => ⟨good.checked.fields request.value.entry.key request.value ready.2,ready.1,
        good.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ ready.2⟩)
      guards index childIndex footprint input returned

/-- Cold evaluation and warm hits derive indexed origins from the actual captured request. -/
theorem edge_call {fuel g s r e p h m c n budget request before value after}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request)
    (guards : GuardHeap before.checked.native.machine.heap) (origins : Origins before) :
    Origins after ∧ EdgeLink request.value value := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have initial := begin_good request good ready
  have prior := begin_origins request origins
  have same := (beginEdge_components request before).1
  rw [started] at initial prior same
  have initialGuards : GuardHeap running.checked.native.machine.heap := by rw [same]; exact guards
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
    obtain ⟨final,same,link⟩ := edge_body body initial (initial.edges.checked _ _ found).1 initialGuards prior
    have retained : middle.edgeResults.cells handle = some ⟨owner,.evaluating⟩ := same ▸ found
    exact ⟨finish_origins handle owner value final retained link,ownerEq ▸ link⟩

open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

private theorem step_inputs (step : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) : Good (caller last) ∧ Inputs last :=
  SourceCurrentOuterPrefixInvariants.reached (.snoc (.refl _) step) good inputs

private def NodeAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeCall fuel g s r e p h m c n budget request before = .done value after →
  Good (width := width) before → NodeReady before request → GuardHeap before.checked.native.machine.heap → Origins before → Origins after
private def BodyAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeBody fuel g s r e p h m c n budget request before = .done value after →
  Good (width := width) before → NodeReady before request → GuardHeap before.checked.native.machine.heap → Origins before → Origins after
private def RowsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  rows fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
  GuardHeap before.checked.native.machine.heap → Origins before → Origins after
private def DescendantsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited value before result after},
  descendants fuel g s r e p h m c n budget inherited value before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → EdgeResident before.checked.native.machine.heap value →
  GuardHeap before.checked.native.machine.heap → Origins before → Origins after
private def ChildrenAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  children fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
  GuardHeap before.checked.native.machine.heap → Origins before → Origins after
private def WalkAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited index values before result after},
  walk fuel g s r e p h m c n budget inherited index values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
  GuardHeap before.checked.native.machine.heap → Origins before → Origins after

private theorem all_done (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited index values before result after actual good ready available guards origins
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
          have current := (ih fuel (Nat.lt_succ_self _)).1 first child.1 child.2 (by exact guards) origins
          obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
          cases last
          have remaining := step_inputs (Step.walk_tail first) good ⟨ready,available⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 rest remaining.1 remaining.2.1 remaining.2.2
            (SourceCurrentOuterGuardHeapReturns.node_done Plain first child.1 child.2 (by exact guards)) current
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready available guards origins
      cases inherited with
      | contradiction =>
        simp only [SourceCurrentAllocatedPartialWorker.children] at actual
        cases actual
        exact origins
      | live identity records => exact walkAt (by simpa only [SourceCurrentAllocatedPartialWorker.children] using actual) good ready available guards origins
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before result after actual good ready resident guards origins
      obtain ⟨combined,prefixDone,_,_,_,_⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
        value.entry.key.constraint inherited before.checked.operations good.checked.operations ready
        (good.checked.fields value.entry.key value resident)
      obtain ⟨values,middle,first,last⟩ := bind_done _ _
        (by simpa only [descendants,prefixDone] using actual)
      have start := step_inputs (Step.descendants_children (fuel := fuel) prefixDone
        (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)) good ⟨ready,resident⟩
      have current := childrenAt first start.1 start.2.1 start.2.2 (by exact guards) origins
      cases last
      exact current
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready resident guards origins
      cases values with
      | nil => simp only [rows] at actual; cases actual; exact origins
      | cons value values =>
        cases fuel with
        | zero => simp only [rows] at actual; cases actual
        | succ fuel =>
          obtain ⟨narrowed,middle,first,later⟩ := bind_done _ _ (by simpa only [rows] using actual)
          have current := (edge_call first good ⟨ready,resident _ List.mem_cons_self⟩ guards origins).1
          obtain ⟨head,afterChildren,childrenDone,last⟩ := bind_done _ _ later
          have child := step_inputs (Step.rows_edge (rest := values) first) good ⟨ready,resident⟩
          have next := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 childrenDone child.1 child.2.1 child.2.2
            (SourceCurrentOuterGuardHeapReturns.edge_done Plain first good ⟨ready,resident _ List.mem_cons_self⟩ guards) current
          obtain ⟨tail,final,rest,done⟩ := bind_done _ _ last
          cases done
          have remaining := step_inputs (Step.rows_tail first childrenDone) good ⟨ready,resident⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.1 rest remaining.1 remaining.2.1 remaining.2.2
            (SourceCurrentOuterGuardHeapReturns.descendants_done Plain childrenDone child.1 child.2.1 child.2.2
              (SourceCurrentOuterGuardHeapReturns.edge_done Plain first good ⟨ready,resident _ List.mem_cons_self⟩ guards)) next
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready guards origins
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
            have current := (ih fuel (Nat.lt_succ_self _)).2.2.1 first good ready.1 resident guards origins
            cases last
            exact current
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready guards origins
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
        have final := bodyAt body current.1 current.2 (by
          have same := (beginNode_components request before).1
          rw [started] at same
          rw [same]
          exact guards) prior
        cases finished
        exact final
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

/-- Every actual completed outer node preserves indexed row origins in all returned edge cells. -/
theorem node_done {fuel g s r e p h m c n budget request before value after}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : NodeReady before request)
    (guards : GuardHeap before.checked.native.machine.heap) (origins : Origins before) :
    Origins after := (all_done fuel).1 actual good ready guards origins

private theorem step_origins (actual : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first)
    (guards : GuardHeap (caller first).checked.native.machine.heap) (origins : Origins (caller first)) :
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
  | rows_edge actual => exact (edge_call actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ guards origins).1
  | rows_tail edge children =>
    have current := (edge_call edge good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ guards origins).1
    have child := step_inputs (Step.rows_edge edge) good inputs
    exact (all_done _).2.2.2.1 children child.1 child.2.1 child.2.2
      (SourceCurrentOuterGuardHeapReturns.edge_done Plain edge good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ guards) current
  | descendants_children | children_walk | walk_head => exact origins
  | walk_tail actual =>
    have child := step_inputs (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) Step.walk_head good inputs
    exact node_done actual child.1 child.2 (by exact guards) origins

/-- Actual unfinished prefixes preserve the indexed origin laws of their initial edge tables. -/
theorem reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first)
    (guards : GuardHeap (caller first).checked.native.machine.heap) (origins : Origins (caller first)) :
    Origins (caller last) := by
  induction actual with
  | refl => exact origins
  | snoc earlier last ih =>
    have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
    exact step_origins last current.1 current.2
      (SourceCurrentOuterGuardHeapReturns.reached Plain earlier good inputs guards) ih

end OuterExecution
end MicroCFTA.SourceCurrentOuterPositionalOrigins

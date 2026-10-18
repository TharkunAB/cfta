import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentOuterInheritedGain
import MicroCFTA.SourceCurrentParentOperationInvariants

/-!
# Full row fields through actual outer requests

Actual Parent returns retain the original full field or the plain sentinel.
Returned outer cells retain the field of their captured edge request.
Warm hits use actual key equality and resident edge identity.
-/
namespace MicroCFTA.SourceCurrentOuterRowFieldOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants
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
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat}

/-- A returned row retains its full source field or the plain rejection field. -/
def Fields (symbol : Symbol) (original : Guard) (result : Edge) : Prop :=
  result.entry.key.symbol = symbol ∧
    (result.entry.key.constraint = original ∨ result.entry.key.constraint = top)

private theorem raw_fields [DecidableEq (EdgeKey Symbol Guard)] (before : Checked width)
    (good : NativeGood before) (symbol : Symbol) (field : Guard) (children : List Node)
    (available : Values before.native.machine.heap children) :
    (run (makeEdge symbol field children) before.native.machine.heap).1.entry.key.symbol = symbol ∧
      (run (makeEdge symbol field children) before.native.machine.heap).1.entry.key.constraint = field := by
  have actual := MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
    good.semantic.ready.semantic.1.normal.facts symbol field children available
  exact ⟨actual.1,actual.2.1⟩

private theorem reject_fields [DecidableEq (EdgeKey Symbol Guard)] (before : Checked width)
    (good : NativeGood before) (symbol : Symbol) (original : Guard) :
    Fields symbol original (SourceCurrentAllocatedMkEdge.reject symbol before).1 := by
  have actual := raw_fields before good symbol top [.empty]
    (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
  exact ⟨actual.1,Or.inr actual.2⟩

private theorem build_fields [DecidableEq (EdgeKey Symbol Guard)]
    {symbol loaded children before result after}
    (actual : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result,after))
    (good : NativeGood (before : Checked width))
    (loadedReady : EqReady before.operations.constraints loaded.stored)
    (available : Values before.native.machine.heap children) :
    Fields symbol (SourceEqualityConjoinAllocation.readback loaded) result := by
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard children
    before.operations before.native.machine.heap good.operations loadedReady
  cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
  | true =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = true := keep
    have equation : SourceCurrentAllocatedMkEdge.build symbol loaded children before =
        (.ok (run (makeEdge symbol (SourceEqualityConjoinAllocation.readback loaded) children) before.native.machine.heap).1,
          SourceCurrentAllocatedQueryMemo.advancePhysical before
            ⟨(run (makeEdge symbol (SourceEqualityConjoinAllocation.readback loaded) children) before.native.machine.heap).2,
            (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).2⟩) := by
      simp only [SourceCurrentAllocatedMkEdge.build,built.1,SourceEqualityMkEdgeAllocation.work,
        SourceEqualityMkEdgeAllocation.outputState,selected,ite_true]
      rfl
    have same := Except.ok.inj (congrArg Prod.fst (equation.symm.trans actual))
    cases same
    have fields := raw_fields before good symbol (SourceEqualityConjoinAllocation.readback loaded) children available
    exact ⟨fields.1,Or.inl fields.2⟩
  | false =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = false := keep
    have equation : SourceCurrentAllocatedMkEdge.build symbol loaded children before =
        (.ok (run (makeEdge symbol top [.empty]) before.native.machine.heap).1,
          SourceCurrentAllocatedQueryMemo.advancePhysical before
            ⟨(run (makeEdge symbol top [.empty]) before.native.machine.heap).2,
            SourceEqualityMkEdgeAllocation.emptyField
              (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).2⟩) := by
      simp only [SourceCurrentAllocatedMkEdge.build,built.1,SourceEqualityMkEdgeAllocation.work,
        SourceEqualityMkEdgeAllocation.outputState,selected,Bool.false_eq_true,ite_false]
    have same := Except.ok.inj (congrArg Prod.fst (equation.symm.trans actual))
    cases same
    have fields := raw_fields before good symbol top [.empty]
      (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
    exact ⟨fields.1,Or.inr fields.2⟩

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

/-- Initial physical inputs and an actual Parent return derive its complete row-field origin. -/
theorem parent
    {g s r e p h m c n budget symbol original inherited children before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children
      before fourth memo = .done result after saved current)
    (good : NativeGood (before : Checked width))
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧
      Values before.native.machine.heap children) : Fields symbol original result := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    exact reject_fields before good symbol original
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
        obtain ⟨effect,_retained,known⟩ := SourceCurrentParentOperationInvariants.reduce reduced good stored
          properties.1 inheritedReady available
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk returned checked =>
          cases returned with
          | error => simp only [SourceCurrentAllocatedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedParentWorker.build,observed] at last
            cases last
            have fields := build_fields observed effect.good
              (properties.1.grows effect.operations.constraint_growth) known
            simpa only [properties.2] using fields

end ParentExecution

/-- Every returned edge cell retains the full field of its captured request. -/
def Origins (before : Caller width) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key)
    (fun cell : FlatMemoThunk.Cell EdgeRequest Edge =>
      ∀ result, cell.status = .returned result →
        Fields cell.request.value.entry.key.symbol cell.request.value.entry.key.constraint result)
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
    (fields : Fields owner.value.entry.key.symbol owner.value.entry.key.constraint value) :
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
      Fields request.value.entry.key.symbol request.value.entry.key.constraint value := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody,observed] at actual; cases actual
  | done result checked fourth memo =>
    simp only [edgeBody,observed] at actual
    cases actual
    exact ⟨origins,rfl,parent observed good.checked good.stored
      (fun _ => ⟨good.checked.fields request.value.entry.key request.value ready.2,ready.1,
        good.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ ready.2⟩)⟩

/-- Cold evaluation and warm hits derive full row fields from their actual captured edge request. -/
theorem edge_call {fuel g s r e p h m c n budget request before value after}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request) (origins : Origins before) :
    Origins after ∧ Fields request.value.entry.key.symbol request.value.entry.key.constraint value := by
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

/-- Every actual completed outer node preserves captured row fields in all returned edge cells. -/
theorem node_done {fuel g s r e p h m c n budget request before value after}
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

/-- Actual unfinished prefixes preserve the field laws derived from their initial edge tables. -/
theorem reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (origins : Origins (caller first)) :
    Origins (caller last) := by
  induction actual with
  | refl => exact origins
  | snoc earlier last ih =>
    have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
    exact step_origins last current.1 current.2 ih

/-- An actual body prefix reaches descendants only after its exact earlier edge call. -/
theorem descendants_source {g s r e p h m c n budget ownerFuel fuel : Nat}
    {owner : NodeRequest} {running before : Caller width} {inherited : EqValue} {edge : Edge}
    (actual : Reached g s r e p h m c n budget (.body ownerFuel owner running)
      (.descendants fuel inherited edge before))
    (good : Good running) (inputs : NodeReady running owner) (origins : Origins running) :
    ∃ original rest start,
      Reached g s r e p h m c n budget (.body ownerFuel owner running)
        (.rows (fuel + 1) inherited (original :: rest) start) ∧
      edgeCall fuel g s r e p h m c n budget ⟨inherited,original⟩ start = .done edge before ∧
      Fields original.entry.key.symbol original.entry.key.constraint edge := by
  cases actual with
  | snoc earlier last =>
    cases last with
    | rows_edge completed =>
      have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
      have retained := reached earlier good inputs origins
      exact ⟨_,_,_,earlier,completed,
        (edge_call completed current.1 ⟨current.2.1,current.2.2 _ List.mem_cons_self⟩ retained).2⟩

/-- A strict height-gain event retains the exact earlier original row and its completed outer edge call. -/
def GainSource (g s r e p h m c n budget : Nat) (first last : Phase width) : Prop :=
  ∃ fuel input edge before output original rest start,
    Reached g s r e p h m c n budget first (.rows (fuel + 1) input (original :: rest) start) ∧
    edgeCall fuel g s r e p h m c n budget ⟨input,original⟩ start = .done edge before ∧
    edge.entry.key.symbol = original.entry.key.symbol ∧
    edge.entry.key.constraint = original.entry.key.constraint ∧
    (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint input before.checked.operations).1 = .ok (some output) ∧
    Reached g s r e p h m c n budget
      (.children fuel output edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge input)) last ∧
    Good before ∧ Inputs (.descendants fuel input edge before) ∧
    SourceCurrentEqualityOperationFixed.FixedPayload input.payload ∧
    SourceCurrentEqualityOperationFixed.FixedPayload output.payload ∧
    SourceCurrentOuterInheritedDescent.pathHeight input < SourceCurrentOuterInheritedDescent.pathHeight output ∧
    ∃ classes, SourceCompactGuards.sourceEqualities original.entry.key.constraint = some classes ∧ classes ≠ []

/-- Initial captured-cell origins turn an actual height gain into an exact earlier full-row source. -/
theorem gain_source {g s r e p h m c n budget ownerFuel : Nat} {owner : NodeRequest}
    {running : Caller width} {last : Phase width}
    (gain : SourceCurrentOuterInheritedGain.HeightGain g s r e p h m c n budget (.body ownerFuel owner running) last)
    (good : Good running) (inputs : NodeReady running owner) (origins : Origins running) :
    GainSource g s r e p h m c n budget (.body ownerFuel owner running) last := by
  obtain ⟨fuel,input,edge,before,output,past,prefixDone,remaining,current,known,inputFixed,outputFixed,increase,nonempty,_⟩ := gain
  obtain ⟨original,rest,start,earlier,completed,fields⟩ := descendants_source past good inputs origins
  have exactField : edge.entry.key.constraint = original.entry.key.constraint := by
    rcases fields.2 with same | plain
    · exact same
    · obtain ⟨classes,found,nonempty⟩ := nonempty
      have emptyOwn : SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some [] := by
        rw [plain]
        rfl
      have empty := Option.some.inj (found.symm.trans emptyOwn)
      exact False.elim (nonempty empty)
  refine ⟨fuel,input,edge,before,output,original,rest,start,earlier,completed,fields.1,exactField,
    prefixDone,remaining,current,known,inputFixed,outputFixed,increase,?_⟩
  simpa only [exactField] using nonempty

/-- Initial physical facts and an actual busy failure derive exact row sources for its nonempty owner. -/
theorem initial_busy {g s r e p h m c n budget handle : Nat} (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (fuel : Nat) (request : NodeRequest) (good : SourceCurrentNativeOperationHeap.Good checked)
    (stored : SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap memo)
    (probes : InternedFreshOrdinaryProbeHeap.Heap checked.native.machine.heap)
    (ready : EqReady checked.operations.constraints request.inherited)
    (available : InternedProbeProvenance.Available checked.native.machine.heap request.value)
    {after : Caller width}
    (actual : nodeCall fuel g s r e p h m c n budget request
      (SourceCurrentAllocatedPartialState.initial checked memo fourth) = .failed (.nodeMemo handle .busy) after) :
    ∃ next candidate,
      Good after ∧ NodeReady after candidate ∧ Origins after ∧
      Reached g s r e p h m c n budget
        (.node fuel request (SourceCurrentAllocatedPartialState.initial checked memo fourth)) (.node next candidate after) ∧
      beginNode candidate after = (handle,.busy,after) ∧
      after.nodeResults.cells handle = some ⟨candidate,.evaluating⟩ ∧
      ∀ identity records, candidate.inherited = .live identity records → records ≠ [] →
        ∃ ownerFuel original entered running,
          Reached g s r e p h m c n budget
            (.node fuel request (SourceCurrentAllocatedPartialState.initial checked memo fourth)) (.node ownerFuel original entered) ∧
          beginNode original entered = (handle,.evaluate candidate,running) ∧
          GainSource g s r e p h m c n budget (.body ownerFuel candidate running) (.node next candidate after) := by
  obtain ⟨next,candidate,final,current,past,busy,present,gains⟩ :=
    SourceCurrentOuterInheritedGain.initial_busy checked memo fourth fuel request good stored probes ready available actual
  have entry := SourceCurrentOuterPrefixInvariants.initial checked memo fourth good stored probes
  have initialOrigins := initial checked memo fourth
  refine ⟨next,candidate,final,current,reached past entry ⟨ready,available⟩ initialOrigins,past,busy,present,?_⟩
  intro identity records shape nonempty
  obtain ⟨ownerFuel,original,entered,running,earlier,started,gain⟩ := gains identity records shape nonempty
  have atCall := SourceCurrentOuterPrefixInvariants.reached earlier entry ⟨ready,available⟩
  have atBody := SourceCurrentOuterPrefixInvariants.activate started atCall.1 atCall.2
  have bodyOrigins := reached (.snoc earlier (.node_evaluate started)) entry ⟨ready,available⟩ initialOrigins
  exact ⟨ownerFuel,original,entered,running,earlier,started,gain_source gain atBody.1 atBody.2 bodyOrigins⟩

end OuterExecution
end MicroCFTA.SourceCurrentOuterRowFieldOrigins


set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 10000000

namespace MicroCFTA.OuterRowFieldKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady)
open SourceCurrentOuterRowFieldOrigins (Origins Fields)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq Node := by classical exact inferInstance
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [],.top⟩
private def positive : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def expression : Syntax Symbol Guard := .node [.mk ("pair",.top) positive [leaf,leaf]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def child : Node := ((InternedProbeProvenance.children value)[0]?).getD .empty
private def row := ((nodeEdges value)[0]?).getD (run (makeEdge ("pair",.top) positive [child,child]) heap).1
private def first := SourceEqualityConstraintAllocation.construct positive.equalities Cache.emptyState
private def positiveValue : EqValue := match first.1 with | .ok value => value | .error _ => .contradiction
private def second := SourceEqualityConstraintAllocation.construct plain.equalities first.2
private def inherited : EqValue := match second.1 with | .ok value => value | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial second.2
private def checked : SourceEqualityNativeDemand.State 4 :=
  ⟨SourceRecursiveIntersectionThunks.initial 4 ⟨heap,Cache.emptyState⟩,operations⟩
private def cold := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def request : NodeRequest := ⟨inherited,value⟩
private noncomputable def execution := nodeCall 6 2 2 0 0 0 0 0 0 0 0 request cold
private noncomputable def after := execution.state
private def edgeRequest : EdgeRequest := ⟨inherited,row⟩
private theorem constructed : built = .done value heap := by
  obtain ⟨result,after,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,value,heap,done,InternedNestedConstruction.Outcome.state]
private theorem first_done : first = (.ok positiveValue,first.2) := by cbv
private theorem second_done : second = (.ok inherited,second.2) := by cbv
private theorem positive_cached : SourceEqualityGuardReadback.Cached positive.equalities := by
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized
    (show EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] by cbv)
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [positive,plain] := by
  exact SourceEqualityOriginalAllocationHistory.History.construct
    (SourceEqualityOriginalAllocationHistory.History.construct (.start Cache.emptyState) positive_cached first_done)
    SourceEqualityGuardReadback.empty_cached second_done
private theorem initial : SourceCurrentConjunctionClassScan.Ready checked ∧ Available heap value := by
  have produced := SourceCurrentConjunctionClassHistoryEntry.constructed 4 history Cache.empty_valid expression
    (fun guard member => by
      have included : guard = positive ∨ guard = plain := by
        simpa [expression,leaf,SourceEqualityConstraintOrigins.guards,
          SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards] using member
      rcases included with rfl | rfl
      · exact .head _
      · exact .tail _ (.head _)) value heap constructed
  exact ⟨produced.1,produced.2.1⟩
private theorem inherited_ready : SourceEqualityConstraintAllocation.Ready operations.constraints inherited := by
  have firstHistory := SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) positive_cached first_done
  obtain ⟨result,after,done,_,ready,_,_,_⟩ := SourceEqualityConstraintAllocation.construct_complete
    plain.equalities SourceEqualityGuardReadback.empty_cached first.2 (firstHistory.verified Cache.empty_valid).1
  obtain ⟨same,state⟩ := Prod.mk.inj (done.symm.trans second_done)
  cases Except.ok.inj same
  cases state
  exact ready
private theorem cold_good : Good cold := SourceCurrentOuterPrefixInvariants.initial checked _ _
  (SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.1.good) initial.1.semantic initial.1.costs)
  (SourceCurrentMemoMergeEffects.stored_empty heap)
  (SourceCurrentMuReconstructionEffects.constructed expression value heap constructed)
private theorem row_resident : EdgeResident heap row := by
  have found : row ∈ nodeEdges value := by cbv; exact .head _
  exact resident_edges heap cold_good.checked.heap.semantic.1.normal.facts.linked
    value initial.2.resident row found
private theorem actual : execution = .done value after := by cbv
private theorem complete_facts : Good after ∧
    SourceCurrentLowerOperationInvariants.Effect cold.checked after.checked ∧
    Available after.checked.native.machine.heap value :=
  SourceCurrentOuterPrefixInvariants.node_done actual cold_good ⟨inherited_ready,initial.2⟩
private theorem origins : Origins after := SourceCurrentOuterRowFieldOrigins.node_done
  actual cold_good ⟨inherited_ready,initial.2⟩ (SourceCurrentOuterRowFieldOrigins.initial checked _ _)
private theorem edge_ready : EdgeReady after edgeRequest := by
  exact ⟨inherited_ready.grows complete_facts.2.1.operations.constraint_growth,
    row_resident.grows complete_facts.2.1.keeps.growth⟩
private theorem ready_hit : beginEdge edgeRequest after = (0,.ready row,after) := by cbv
private theorem warm : edgeCall 0 2 2 0 0 0 0 0 0 0 0 edgeRequest after = .done row after :=
  edgeCall_ready 0 2 2 0 0 0 0 0 0 0 0 edgeRequest after after 0 row ready_hit
private theorem phase_reached : Reached 2 2 0 0 0 0 0 0 0 0
    (.rows 1 inherited [row] after) (.descendants 0 inherited row after) :=
  Reached.snoc (.refl _) (Step.rows_edge warm)
private theorem row_positive : row.entry.key.constraint = positive := by cbv
private theorem positive_not_top : positive ≠ SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula) := by
  intro same
  have falseEquality := congrArg SourceSymbolicIndex.Constraint.equalities same
  cases falseEquality
private theorem fixture :
    Good cold ∧ Origins cold ∧ NodeReady cold request ∧
      execution = .done value after ∧ Good after ∧ Origins after ∧
      beginEdge edgeRequest after = (0,.ready row,after) ∧
      edgeCall 0 2 2 0 0 0 0 0 0 0 0 edgeRequest after = .done row after ∧
      Fields row.entry.key.symbol row.entry.key.constraint row ∧
      row.entry.key.constraint = positive ∧
      row.entry.key.constraint ≠ SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula) ∧
      Reached 2 2 0 0 0 0 0 0 0 0 (.rows 1 inherited [row] after) (.descendants 0 inherited row after) ∧
      Origins (SourceCurrentOuterActiveAncestry.caller (.descendants 0 inherited row after)) := by
  have retained := SourceCurrentOuterRowFieldOrigins.edge_call warm complete_facts.1 edge_ready origins
  have earlierInputs : SourceCurrentOuterPrefixInvariants.Inputs (.rows 1 inherited [row] after) :=
    ⟨edge_ready.1,by intro edge member; cases List.mem_singleton.mp member; exact edge_ready.2⟩
  exact ⟨cold_good,SourceCurrentOuterRowFieldOrigins.initial checked _ _,⟨inherited_ready,initial.2⟩,
    actual,complete_facts.1,origins,ready_hit,warm,retained.2,row_positive,
    by rw [row_positive]; exact positive_not_top,phase_reached,
    SourceCurrentOuterRowFieldOrigins.reached phase_reached complete_facts.1 earlierInputs origins⟩

/-- An actual cold node return supplies row origins before a positive-field warm edge hit and descendants prefix. -/
theorem cold_node_warm_positive_row :
    Good cold ∧ Origins cold ∧ NodeReady cold request ∧
      execution = .done value after ∧ Good after ∧ Origins after ∧
      beginEdge edgeRequest after = (0,.ready row,after) ∧
      edgeCall 0 2 2 0 0 0 0 0 0 0 0 edgeRequest after = .done row after ∧
      Fields row.entry.key.symbol row.entry.key.constraint row ∧
      row.entry.key.constraint = positive ∧
      row.entry.key.constraint ≠ SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula) ∧
      Reached 2 2 0 0 0 0 0 0 0 0 (.rows 1 inherited [row] after) (.descendants 0 inherited row after) ∧
      Origins (SourceCurrentOuterActiveAncestry.caller (.descendants 0 inherited row after)) := fixture

end MicroCFTA.OuterRowFieldKernels

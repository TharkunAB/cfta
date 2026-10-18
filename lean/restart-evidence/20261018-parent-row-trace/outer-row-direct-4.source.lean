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
    change FlatMemoThunk.demand published.1 published.2 = (.ready result,running.edgeResults) at observed
    obtain ⟨owner,found,same⟩ := FlatMemoThunk.demand_ready_original _ _ result _ observed
    rw [← same] at found
    have handles : published.1 = handle := congrArg Prod.fst started
    rw [handles] at found
    have ownerEq := begin_request initial ready started found
    exact ⟨prior,ownerEq ▸ prior.checked _ _ found result rfl⟩
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
    exact ⟨finish_origins handle owner result final retained fields,ownerEq ▸ fields⟩

end MicroCFTA.SourceCurrentOuterRowFieldOrigins

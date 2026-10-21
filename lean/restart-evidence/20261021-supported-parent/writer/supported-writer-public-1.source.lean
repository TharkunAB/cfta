import MicroCFTA.SourceCurrentOuterMergePositionSupport
import MicroCFTA.SourceCurrentOuterParentHistory
import MicroCFTA.SourceCurrentOuterUnionNormalHistory
import MicroCFTA.SourceCurrentOuterGuardHeapReturns
import MicroCFTA.SourceCurrentOuterOwnerSelection
import MicroCFTA.SourceCurrentParentGuardHeapReturns
import MicroCFTA.SourceCurrentUnionNormalScan

/-!
# Support and causal heap facts at the same historical Parent writer

Cold publication records three entry laws with its exact Parent execution.
Warm hits recover that certificate for the same complete captured request.
Actual outer prefixes need no future root return. Internal failures are outside
this contract. GuardHeap Plain records Mu profile equality, not plainness of
all stored guards.
-/
namespace MicroCFTA.SourceCurrentOuterSupportedParentHistory
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
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Support" => SourceCurrentMergePositivePosition.Support
local notation "UnionNormal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeGood" => SourceCurrentNativeOperationHeap.Good
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable {width : Nat}

private abbrev Entry (before : Caller width) : Prop :=
  Support before.merge ∧ UnionNormal before.checked.native.machine.heap ∧
    GuardHeap Plain before.checked.native.machine.heap

/-- One actual Parent writer retains support, normality, and Mu guard profiles at its same entry. -/
def SupportedWritten [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] (request : EdgeRequest) (result : Edge) : Prop :=
  ∃ (g s r e p h m c n budget : Nat) (before after : Checked width)
    (fourth savedFourth : Fourth) (memo saved : Memo),
    SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
      request.value.children before fourth memo = .done result after savedFourth saved ∧
    NativeGood before ∧ SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo ∧
    Support memo ∧ UnionNormal before.native.machine.heap ∧ GuardHeap Plain before.native.machine.heap ∧
    (SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
      FieldAvailable before.operations request.value.entry.key.constraint ∧
      EqReady before.operations.constraints request.inherited ∧
      Values before.native.machine.heap request.value.children)

/-- Each returned edge cell retains its same captured request and supported historical writer. -/
def SupportedOrigins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] (before : Caller width) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key)
    (fun cell : FlatMemoThunk.Cell EdgeRequest Edge =>
      ∀ result, cell.status = .returned result →
        SupportedWritten (width := width) cell.request result)
    before.edgeResults

/-- Empty edge tables require no historical writer premise. -/
theorem initial [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] (checked : Checked width) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (fourth : SourceCurrentEmptinessMemo.Memo) : SupportedOrigins (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
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

private theorem begin_origins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] (request : EdgeRequest) {before : Caller width} (origins : SupportedOrigins before) :
    SupportedOrigins (beginEdge request before).2.2 := by
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

private theorem finish_origins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] (handle : Nat) (owner : EdgeRequest) (value : Edge) {before : Caller width}
    (origins : SupportedOrigins before) (found : before.edgeResults.cells handle = some ⟨owner,.evaluating⟩)
    (fields : SupportedWritten (width := width) owner value) :
    SupportedOrigins (finishEdge handle value before) := by
  simp only [SupportedOrigins,finishEdge,FlatMemoThunk.finish,found]
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
    (good : Good (width := width) before) (ready : EdgeReady before request) (origins : SupportedOrigins before) (entry : Entry before) :
    SupportedOrigins after ∧ after.edgeResults = before.edgeResults ∧
      SupportedWritten (width := width) request value := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody,observed] at actual; cases actual
  | done result checked fourth memo =>
    simp only [edgeBody,observed] at actual
    cases actual
    exact ⟨origins,rfl,g,s,r,e,p,h,m,c,n,budget,before.checked,checked,
      before.fourth,fourth,before.merge,memo,observed,good.checked,good.stored,entry.1,entry.2.1,entry.2.2,
      fun _ => ⟨good.checked.fields request.value.entry.key request.value ready.2,ready.1,
        good.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ ready.2⟩⟩

/-- Actual cold calls record entry laws and warm hits recover those same historical laws. -/
theorem edge_call {fuel g s r e p h m c n budget request before value after}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request) (origins : SupportedOrigins before)
    (support : Support before.merge) (normal : UnionNormal before.checked.native.machine.heap)
    (guards : GuardHeap Plain before.checked.native.machine.heap) :
    SupportedOrigins after ∧ SupportedWritten (width := width) request value := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have initial := begin_good request good ready
  have prior := begin_origins request origins
  have entry : Entry (beginEdge request before).2.2 := by
    have components := beginEdge_components request before
    refine ⟨?_,?_,?_⟩
    · rw [components.2.1]; exact support
    · rw [components.1]; exact normal
    · rw [components.1]; exact guards
  rw [started] at initial prior entry
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
    obtain ⟨final,same,fields⟩ := edge_body body initial (initial.edges.checked _ _ found).1 prior entry
    have retained : middle.edgeResults.cells handle = some ⟨owner,.evaluating⟩ := same ▸ found
    exact ⟨finish_origins handle owner value final retained fields,ownerEq ▸ fields⟩

open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

private theorem step_inputs (step : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) : Good (caller last) ∧ Inputs last :=
  SourceCurrentOuterPrefixInvariants.reached (.snoc (.refl _) step) good inputs

private theorem entry_reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (entry : Entry (caller first)) :
    Entry (caller last) :=
  ⟨SourceCurrentOuterMergePositionSupport.reached actual good inputs entry.1,
    SourceCurrentOuterUnionNormalHistory.reached actual entry.2.1,
    SourceCurrentOuterGuardHeapReturns.reached Plain actual good inputs entry.2.2⟩

private def NodeAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeCall fuel g s r e p h m c n budget request before = .done value after →
  Good (width := width) before → NodeReady before request → Entry before → SupportedOrigins before → SupportedOrigins after
private def BodyAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeBody fuel g s r e p h m c n budget request before = .done value after →
  Good (width := width) before → NodeReady before request → Entry before → SupportedOrigins before → SupportedOrigins after
private def RowsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  rows fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
  Entry before → SupportedOrigins before → SupportedOrigins after
private def DescendantsAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited value before result after},
  descendants fuel g s r e p h m c n budget inherited value before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → EdgeResident before.checked.native.machine.heap value →
  Entry before → SupportedOrigins before → SupportedOrigins after
private def ChildrenAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  children fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
  Entry before → SupportedOrigins before → SupportedOrigins after
private def WalkAt (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited index values before result after},
  walk fuel g s r e p h m c n budget inherited index values before = .done result after → Good (width := width) before →
  EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
  Entry before → SupportedOrigins before → SupportedOrigins after

private theorem all_done (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited index values before result after actual good ready available entry origins
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
          have current := (ih fuel (Nat.lt_succ_self _)).1 first child.1 child.2 (by exact entry) origins
          obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
          cases last
          have remaining := step_inputs (Step.walk_tail first) good ⟨ready,available⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 rest remaining.1 remaining.2.1 remaining.2.2
            (entry_reached (.snoc (.refl _) (.walk_tail first)) good ⟨ready,available⟩ entry) current
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready available entry origins
      cases inherited with
      | contradiction =>
        simp only [SourceCurrentAllocatedPartialWorker.children] at actual
        cases actual
        exact origins
      | live identity records => exact walkAt (by simpa only [SourceCurrentAllocatedPartialWorker.children] using actual) good ready available entry origins
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before result after actual good ready resident entry origins
      obtain ⟨combined,prefixDone,_,_,_,_⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
        value.entry.key.constraint inherited before.checked.operations good.checked.operations ready
        (good.checked.fields value.entry.key value resident)
      obtain ⟨values,middle,first,last⟩ := bind_done _ _
        (by simpa only [descendants,prefixDone] using actual)
      have start := step_inputs (Step.descendants_children (fuel := fuel) prefixDone
        (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)) good ⟨ready,resident⟩
      have current := childrenAt first start.1 start.2.1 start.2.2 (by exact entry) origins
      cases last
      exact current
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready resident entry origins
      cases values with
      | nil => simp only [rows] at actual; cases actual; exact origins
      | cons value values =>
        cases fuel with
        | zero => simp only [rows] at actual; cases actual
        | succ fuel =>
          obtain ⟨narrowed,middle,first,later⟩ := bind_done _ _ (by simpa only [rows] using actual)
          have current := (edge_call first good ⟨ready,resident _ List.mem_cons_self⟩ origins entry.1 entry.2.1 entry.2.2).1
          obtain ⟨head,afterChildren,childrenDone,last⟩ := bind_done _ _ later
          have child := step_inputs (Step.rows_edge (rest := values) first) good ⟨ready,resident⟩
          have next := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 childrenDone child.1 child.2.1 child.2.2
            (entry_reached (.snoc (.refl _) (.rows_edge first)) good ⟨ready,resident⟩ entry) current
          obtain ⟨tail,final,rest,done⟩ := bind_done _ _ last
          cases done
          have remaining := step_inputs (Step.rows_tail first childrenDone) good ⟨ready,resident⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.1 rest remaining.1 remaining.2.1 remaining.2.2
            (entry_reached (.snoc (.refl _) (.rows_tail first childrenDone)) good ⟨ready,resident⟩ entry) next
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready entry origins
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
        | node identity originals depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
            obtain ⟨rebuilt,middle,first,last⟩ := bind_done _ _ (by simpa only [nodeBody] using actual)
            have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ ready.2.resident
            have current := (ih fuel (Nat.lt_succ_self _)).2.2.1 first good ready.1 resident entry origins
            cases last
            exact current
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready entry origins
      rcases started : beginNode request before with ⟨handle,action,running⟩
      have unchanged : (beginNode request before).2.2.edgeResults = before.edgeResults := rfl
      rw [started] at unchanged
      have prior : SupportedOrigins running := by change FlatMemoThunk.Valid _ _ running.edgeResults; rw [unchanged]; exact origins
      cases action with
      | busy | absent => simp only [nodeCall,started] at actual; cases actual
      | ready result => simp only [nodeCall,started] at actual; cases actual; exact prior
      | evaluate original =>
        obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [nodeCall,started] using actual)
        have current := SourceCurrentOuterPrefixInvariants.activate started good ready
        have final := bodyAt body current.1 current.2
          (entry_reached (g := g) (s := s) (r := r) (e := e) (p := p) (h := h)
            (m := m) (c := c) (n := n) (budget := budget) (first := .node fuel request before)
            (.snoc (.refl _) (.node_evaluate started)) good ready entry) prior
        cases finished
        exact final
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

private theorem node_done {fuel g s r e p h m c n budget request before value after}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : NodeReady before request) (entry : Entry before) (origins : SupportedOrigins before) :
    SupportedOrigins after := (all_done fuel).1 actual good ready entry origins

private theorem step_origins (actual : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (entry : Entry (caller first)) (origins : SupportedOrigins (caller first)) :
    SupportedOrigins (caller last) := by
  cases actual with
  | node_evaluate started =>
    have same := congrArg (fun result => result.2.2.edgeResults) started
    unfold SupportedOrigins at *
    dsimp only [Prod.snd] at same
    dsimp only [SourceCurrentOuterActiveAncestry.caller] at origins ⊢
    rw [← same]
    exact origins
  | body_rows => exact origins
  | rows_edge actual => exact (edge_call actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins entry.1 entry.2.1 entry.2.2).1
  | rows_tail edge children =>
    have current := (edge_call edge good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ origins entry.1 entry.2.1 entry.2.2).1
    have child := step_inputs (Step.rows_edge edge) good inputs
    exact (all_done _).2.2.2.1 children child.1 child.2.1 child.2.2
      (entry_reached (.snoc (.refl _) (.rows_edge edge)) good inputs entry) current
  | descendants_children | children_walk | walk_head => exact origins
  | walk_tail actual =>
    have child := step_inputs (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) Step.walk_head good inputs
    exact node_done actual child.1 child.2 (by exact entry) origins

/-- Actual unfinished outer prefixes preserve supported historical writers. -/
theorem reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (origins : SupportedOrigins (caller first))
    (support : Support (caller first).merge) (normal : UnionNormal (caller first).checked.native.machine.heap)
    (guards : GuardHeap Plain (caller first).checked.native.machine.heap) :
    SupportedOrigins (caller last) := by
  induction actual with
  | refl => exact origins
  | snoc earlier last ih =>
    have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
    exact step_origins last current.1 current.2
      (entry_reached earlier good inputs ⟨support,normal,guards⟩) ih

end OuterExecution

end MicroCFTA.SourceCurrentOuterSupportedParentHistory

namespace MicroCFTA.SourceCurrentOuterSupportedParentHistory
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good EdgeReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Support" => SourceCurrentMergePositivePosition.Support
local notation "UnionNormal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Origins" => SupportedOrigins
variable {width : Nat}
private theorem prefix_good {loaded : Allocated} {inherited : SourceEqualityConstraintAllocation.Value}
    {original : Guard} {before : Checked width} (good : SourceCurrentNativeOperationHeap.Good before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : EqReady before.operations.constraints inherited) :
    SourceCurrentNativeOperationHeap.Good (prefixState before loaded inherited) := by
  have ready := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
    good.operations.constraints cached loaded found
  have constructor := SourceEqualityConstraintFieldLookup.load_constructor_receipt original
    before.operations.constraints cached loaded found
  obtain ⟨_, _, _, _, _, valid, growth⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct loaded.stored loaded.guard inherited before.operations
      good.operations ready.1 inheritedReady original.equalities cached constructor
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
      ⟨before.native.machine.heap,
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).2⟩ :=
    ⟨SourceEqualityRequiredCache.pure_keeps _ good.heap,
      ⟨good.semantic, good.costs, valid, good.fields.grows growth⟩, growth⟩
  exact good.advance _ effects

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A selected owner copy retains the same writer and the causal facts at its final Scan. -/
theorem selected {fuel g s r e p h m c n budget handle index : Nat}
    {request : EdgeRequest} {owner : NodeRequest} {before after : Caller width}
    {returned : Edge} {child : Node} {ownerEntry ownerDepth ownerFree}
    {ownerRows : List Edge}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done returned after)
    (good : Good before) (ready : EdgeReady before request) (origins : Origins before)
    (support : Support before.merge) (normal : UnionNormal before.checked.native.machine.heap)
    (guards : GuardHeap Plain before.checked.native.machine.heap)
    (active : before.nodeResults.cells handle = some ⟨owner,.evaluating⟩)
    (ordinary : owner.value = .node ownerEntry ownerRows ownerDepth ownerFree)
    (member : request.value ∈ ownerRows)
    (found : returned.children[index]? = some child)
    (sameReference : child.referenceOf = owner.value.referenceOf) :
    Origins after ∧ child = owner.value ∧
    ∃ (wg ws wr we wp wh wm wc wn wbudget : Nat) (writerBefore writerAfter : Checked width)
      (writerFourth writerSaved : Fourth) (writerMemo writerMerge : Memo),
      SourceCurrentAllocatedParentWorker.edge wg ws wr we wp wh wm wc wn wbudget
        request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
        request.value.children writerBefore writerFourth writerMemo =
          .done returned writerAfter writerSaved writerMerge ∧
      SourceCurrentNativeOperationHeap.Good writerBefore ∧
      SourceCurrentMemoMergeEffects.Stored writerBefore.native.machine.heap writerMemo ∧
      Support writerMemo ∧ UnionNormal writerBefore.native.machine.heap ∧ GuardHeap Plain writerBefore.native.machine.heap ∧
      (SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
        FieldAvailable writerBefore.operations request.value.entry.key.constraint ∧
        EqReady writerBefore.operations.constraints request.inherited ∧
        Values writerBefore.native.machine.heap request.value.children) ∧
      ∃ (loaded : Allocated) (middle : Checked width) (records kept : List Record)
      (scanned : Checked width) (scanFourth : Fourth) (prepared : List Node) (preparedHeap : Heap),
      SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false ∧
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint writerBefore.operations.constraints = .ok (some loaded) ∧
      SourceCurrentAllocatedLocalWorker.reduce wg ws wr we wp wh wm wc wn wbudget loaded request.inherited request.value.children
        writerBefore writerFourth writerMemo = .done returned.children middle writerSaved writerMerge ∧
      SourceCurrentAllocatedMkEdge.build request.value.entry.key.symbol loaded returned.children middle = (.ok returned, writerAfter) ∧
      SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
        returned.children.length = true ∧
      (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard request.inherited writerBefore.operations).1 =
        .ok (.classes records) ∧
      SourceCurrentAllocatedRecordScanWorker.scan wg ws wp wh wn wbudget request.value.children records
        (prefixState writerBefore loaded request.inherited) writerFourth = .done (none, kept) scanned scanFourth ∧
      kept ≠ [] ∧
      SourceEqualityRequiredExecution.requireAll wr wh
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) request.value.children
        scanned.native.machine.heap = .done prepared preparedHeap ∧
      SourceCurrentAllocatedClassWorker.pass we wp wh wm wc wn kept prepared
        (advanceHeap scanned preparedHeap) writerMemo = .done returned.children middle writerMerge ∧
      writerSaved = scanFourth ∧
      UnionNormal scanned.native.machine.heap ∧ GuardHeap Plain scanned.native.machine.heap ∧
      ∀ record ∈ kept, EndpointStatefulGateTrace.ClassTrace source reaches request.value.children record.paths
        scanned.native.machine.heap false scanned.native.machine.heap := by
  obtain ⟨current,effect,resident⟩ := SourceCurrentOuterPrefixInvariants.edge_done actual good ready
  have ownerBefore := (good.nodes.checked _ _ active).1.2
  have ownerAfter := effect.keeps.available owner.value ownerBefore
  have children := current.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ resident
  have childAfter := children child (List.mem_of_getElem? found)
  have same := SourceEqualityPartialKeyTransport.available_reference_eq _
    current.checked.heap.semantic.1.normal.facts.coherent child owner.value childAfter ownerAfter sameReference
  have exactOwner : returned.children[index]? = some (.node ownerEntry ownerRows ownerDepth ownerFree) := by
    rw [same,ordinary] at found
    exact found
  obtain ⟨retained,wg,ws,wr,we,wp,wh,wm,wc,wn,wbudget,writerBefore,writerAfter,
    writerFourth,writerSaved,writerMemo,writerMerge,written,initial,stored,writerSupport,writerNormal,writerGuards,live⟩ :=
    edge_call actual good ready origins support normal guards
  obtain ⟨loaded,middle,records,kept,scanned,scanFourth,prepared,preparedHeap,
    noncontradictory,loadedAt,reduced,built,accepted,precheck,scanCall,nonempty,
    requiredCall,passCall,sameFourth,gates⟩ :=
    SourceCurrentActualOwnerSelection.selected written initial stored live member exactOwner
  obtain ⟨field,inheritedReady,available⟩ := live noncontradictory
  have prefixGood := prefix_good initial field.1 loadedAt inheritedReady
  have prefixAvailable : Values (prefixState writerBefore loaded request.inherited).native.machine.heap request.value.children := available
  have prefixNormal : UnionNormal (prefixState writerBefore loaded request.inherited).native.machine.heap := writerNormal
  have prefixGuards : GuardHeap Plain (prefixState writerBefore loaded request.inherited).native.machine.heap := writerGuards
  have scanNormal := SourceCurrentUnionNormalScan.records wg ws wp wh wn wbudget request.value.children records
    (prefixState writerBefore loaded request.inherited) writerFourth prefixNormal
  rw [scanCall] at scanNormal
  have pathScan := (SourceCurrentAllocatedRecordScanWorker.scan_mapPaths wg ws wp wh wn wbudget request.value.children records
    (prefixState writerBefore loaded request.inherited) writerFourth).symm
  rw [scanCall] at pathScan
  have scanGuards := SourceCurrentParentGuardHeapReturns.scan Plain pathScan prefixGood prefixAvailable prefixGuards
  exact ⟨retained,same,wg,ws,wr,we,wp,wh,wm,wc,wn,wbudget,writerBefore,writerAfter,
    writerFourth,writerSaved,writerMemo,writerMerge,written,initial,stored,writerSupport,writerNormal,writerGuards,live,
    loaded,middle,records,kept,scanned,scanFourth,prepared,preparedHeap,
    noncontradictory,loadedAt,reduced,built,accepted,precheck,scanCall,nonempty,
    requiredCall,passCall,sameFourth,scanNormal,scanGuards,gates⟩

end MicroCFTA.SourceCurrentOuterSupportedParentHistory

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 16384
set_option maxHeartbeats 0

#check @MicroCFTA.SourceCurrentOuterSupportedParentHistory.SupportedWritten
#print MicroCFTA.SourceCurrentOuterSupportedParentHistory.SupportedWritten
#print axioms MicroCFTA.SourceCurrentOuterSupportedParentHistory.SupportedWritten

#check @MicroCFTA.SourceCurrentOuterSupportedParentHistory.SupportedOrigins
#print MicroCFTA.SourceCurrentOuterSupportedParentHistory.SupportedOrigins
#print axioms MicroCFTA.SourceCurrentOuterSupportedParentHistory.SupportedOrigins

#check @MicroCFTA.SourceCurrentOuterSupportedParentHistory.initial
#print MicroCFTA.SourceCurrentOuterSupportedParentHistory.initial
#print axioms MicroCFTA.SourceCurrentOuterSupportedParentHistory.initial

#check @MicroCFTA.SourceCurrentOuterSupportedParentHistory.edge_call
#print MicroCFTA.SourceCurrentOuterSupportedParentHistory.edge_call
#print axioms MicroCFTA.SourceCurrentOuterSupportedParentHistory.edge_call

#check @MicroCFTA.SourceCurrentOuterSupportedParentHistory.reached
#print MicroCFTA.SourceCurrentOuterSupportedParentHistory.reached
#print axioms MicroCFTA.SourceCurrentOuterSupportedParentHistory.reached

#check @MicroCFTA.SourceCurrentOuterSupportedParentHistory.selected
#print MicroCFTA.SourceCurrentOuterSupportedParentHistory.selected
#print axioms MicroCFTA.SourceCurrentOuterSupportedParentHistory.selected

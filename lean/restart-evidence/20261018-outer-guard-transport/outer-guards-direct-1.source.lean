import MicroCFTA.SourceCurrentOuterPrefixInvariants
import MicroCFTA.SourceCurrentParentGuardHeapReturns

/-!
# Causal guard profiles through actual outer calls and prefixes

Initial physical facts and actual earlier returns supply each intermediate
state. The guard predicate can be arbitrary. Successful calls and unfinished
prefixes retain the stored Mu body-to-probe profile law. This law does not
restrict every raw edge guard or prove recursive completion.
-/
namespace MicroCFTA.SourceCurrentOuterGuardHeapReturns
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady Inputs)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Heap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
variable {width : Nat}

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

private theorem begin_good (request : EdgeRequest) {before : Caller width}
    (good : Good before) (ready : EdgeReady before request) : Good (beginEdge request before).2.2 := by
  refine ⟨good.checked,good.stored,good.probes,good.nodes,?_⟩
  apply demand_valid
  · exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.edges rfl
      ⟨ready,by intro value impossible; cases impossible⟩
  · intro owner supported
    exact ⟨supported.1,by intro value impossible; cases impossible⟩

private theorem bind_done (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]

private theorem raw_edge (annotation : Guard → Prop) (edge : Edge) (values : List Node) (before : Checked width)
    (guards : Heap annotation before.native.machine.heap) :
    Heap annotation (SourceCurrentAllocatedRawRebuild.edge edge values before).2.native.machine.heap := by
  exact guards

private theorem raw_node (annotation : Guard → Prop) (original : Node) (oldRows newRows : List Edge)
    (before : Checked width) (guards : Heap annotation before.native.machine.heap) :
    Heap annotation (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).2.native.machine.heap := by
  unfold SourceCurrentAllocatedRawRebuild.modify SourceEqualityPartialNodeRebuild.modify
  split
  · exact guards
  · exact SourceCurrentConstrainedCapGuardHeap.preserve annotation _ _ guards
      (InternedShallowHeap.makeNode_noNewMu newRows _)

variable [DecidableEq Symbol] [DecidableEq Node]

/-- A successful Parent body retains the initial causal Mu guard profiles. -/
theorem edge_body_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget request before value after}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody,observed] at actual; cases actual
  | done result checked fourth memo =>
    simp only [edgeBody,observed] at actual
    cases actual
    exact SourceCurrentParentGuardHeapReturns.parent annotation observed good.checked good.stored guards
      (fun _ => ⟨good.checked.fields request.value.entry.key request.value ready.2,ready.1,
        good.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ ready.2⟩)

/-- Cold edge evaluation and ready hits retain the same causal profile invariant. -/
theorem edge_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget request before value after}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : EdgeReady before request)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have initial := begin_good request good ready
  have same := (beginEdge_components request before).1
  rw [started] at initial same
  have initialGuards : Heap annotation running.checked.native.machine.heap := by rw [same]; exact guards
  cases action with
  | busy | absent => simp only [edgeCall,started] at actual; cases actual
  | ready result =>
    simp only [edgeCall,started] at actual
    cases actual
    exact initialGuards
  | evaluate owner =>
    let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
    have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
    change FlatMemoThunk.demand published.1 published.2 = (.evaluate owner,running.edgeResults) at observed
    have found := (FlatMemoThunk.demand_evaluate _ _ _ owner observed).2
    have handles : published.1 = handle := congrArg Prod.fst started
    rw [handles] at found
    obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [edgeCall,started] using actual)
    cases finished
    exact edge_body_done annotation body initial (initial.edges.checked _ _ found).1 initialGuards

private def NodeAt (annotation : Guard → Prop) (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeCall fuel g s r e p h m c n budget request before = .done value after → Good (width := width) before → NodeReady before request →
    Heap annotation before.checked.native.machine.heap → Heap annotation after.checked.native.machine.heap
private def BodyAt (annotation : Guard → Prop) (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeBody fuel g s r e p h m c n budget request before = .done value after → Good (width := width) before → NodeReady before request →
    Heap annotation before.checked.native.machine.heap → Heap annotation after.checked.native.machine.heap
private def RowsAt (annotation : Guard → Prop) (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  rows fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Heap annotation before.checked.native.machine.heap → Heap annotation after.checked.native.machine.heap
private def DescendantsAt (annotation : Guard → Prop) (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited value before result after},
  descendants fuel g s r e p h m c n budget inherited value before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → EdgeResident before.checked.native.machine.heap value →
    Heap annotation before.checked.native.machine.heap → Heap annotation after.checked.native.machine.heap
private def ChildrenAt (annotation : Guard → Prop) (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  children fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
    Heap annotation before.checked.native.machine.heap → Heap annotation after.checked.native.machine.heap
private def WalkAt (annotation : Guard → Prop) (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited index values before result after},
  walk fuel g s r e p h m c n budget inherited index values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
    Heap annotation before.checked.native.machine.heap → Heap annotation after.checked.native.machine.heap

private theorem all_done (annotation : Guard → Prop) (fuel : Nat) :
    NodeAt (width := width) annotation fuel ∧ BodyAt (width := width) annotation fuel ∧ RowsAt (width := width) annotation fuel ∧
      DescendantsAt (width := width) annotation fuel ∧ ChildrenAt (width := width) annotation fuel ∧ WalkAt (width := width) annotation fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) annotation fuel := by
      intro g s r e p h m c n budget inherited index values before result after actual good ready available guards
      cases values with
      | nil => simp only [walk] at actual; cases actual; exact guards
      | cons value values =>
        cases fuel with
        | zero => simp only [walk] at actual; cases actual
        | succ fuel =>
          obtain ⟨head,middle,first,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
          have start := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .walk (fuel+1) inherited index (value :: values) before)
            (last := .node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before inherited index).1,value⟩
              (SourceCurrentAllocatedPartialGraph.descend before inherited index).2)
            (.snoc (.refl _) .walk_head) good ⟨ready,available⟩
          have headGuards := (ih fuel (Nat.lt_succ_self _)).1 first start.1 start.2 (by exact guards)
          obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
          cases last
          have resumed := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .walk (fuel+1) inherited index (value :: values) before)
            (last := .walk fuel inherited (index+1) values middle)
            (.snoc (.refl _) (.walk_tail first)) good ⟨ready,available⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 rest resumed.1 resumed.2.1 resumed.2.2 headGuards
    have childrenAt : ChildrenAt (width := width) annotation fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready available guards
      cases inherited with
      | contradiction => simp only [SourceCurrentAllocatedPartialWorker.children] at actual; cases actual; exact guards
      | live identity records => exact walkAt (by simpa only [SourceCurrentAllocatedPartialWorker.children] using actual) good ready available guards
    have descendantsAt : DescendantsAt (width := width) annotation fuel := by
      intro g s r e p h m c n budget inherited value before result after actual good ready resident guards
      obtain ⟨combined,prefixDone,_,_,_,_⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
        value.entry.key.constraint inherited before.checked.operations good.checked.operations ready
        (good.checked.fields value.entry.key value resident)
      obtain ⟨values,middle,first,last⟩ := bind_done _ _ (by simpa only [descendants,prefixDone] using actual)
      have start := SourceCurrentOuterPrefixInvariants.reached
        (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
        (first := .descendants fuel inherited value before)
        (last := .children fuel combined value.children (SourceCurrentAllocatedPartialGraph.prefixState before value inherited))
        (.snoc (.refl _) (.descendants_children prefixDone)) good ⟨ready,resident⟩
      have retained := childrenAt first start.1 start.2.1 start.2.2 (by exact guards)
      cases last
      exact raw_edge annotation value values middle.checked retained
    have rowsAt : RowsAt (width := width) annotation fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready resident guards
      cases values with
      | nil => simp only [rows] at actual; cases actual; exact guards
      | cons value values =>
        cases fuel with
        | zero => simp only [rows] at actual; cases actual
        | succ fuel =>
          obtain ⟨narrowed,middle,first,later⟩ := bind_done _ _ (by simpa only [rows] using actual)
          have edgeGuards := edge_done annotation first good ⟨ready,resident _ List.mem_cons_self⟩ guards
          obtain ⟨head,afterChildren,childrenDone,last⟩ := bind_done _ _ later
          have start := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .rows (fuel+1) inherited (value :: values) before)
            (last := .descendants fuel inherited narrowed middle)
            (.snoc (.refl _) (.rows_edge first)) good ⟨ready,resident⟩
          have headGuards := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 childrenDone start.1 start.2.1 start.2.2 edgeGuards
          obtain ⟨tail,final,rest,done⟩ := bind_done _ _ last
          cases done
          have resumed := SourceCurrentOuterPrefixInvariants.reached
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
            (first := .rows (fuel+1) inherited (value :: values) before)
            (last := .rows fuel inherited values afterChildren)
            (.snoc (.refl _) (.rows_tail first childrenDone)) good ⟨ready,resident⟩
          exact (ih fuel (Nat.lt_succ_self _)).2.2.1 rest resumed.1 resumed.2.1 resumed.2.2 headGuards
    have bodyAt : BodyAt (width := width) annotation fuel := by
      intro g s r e p h m c n budget request before value after actual good ready guards
      cases request with
      | mk inherited original =>
        cases original with
        | empty | union => simp only [nodeBody] at actual; cases actual; exact guards
        | reference name => simp only [nodeBody] at actual; cases actual
        | mu entry body depth ordinary =>
          have built := SourceCurrentMuReconstructionEffects.node_body fuel g s r e p h m c n budget
            entry body depth ordinary inherited before good.checked good.probes ready.2
          rw [built] at actual
          cases actual
          exact guards
        | node entry originals depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
            obtain ⟨rebuilt,middle,first,last⟩ := bind_done _ _ (by simpa only [nodeBody] using actual)
            have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ ready.2.resident
            have retained := (ih fuel (Nat.lt_succ_self _)).2.2.1 first good ready.1 resident guards
            cases last
            exact raw_node annotation (.node entry originals depth free) originals rebuilt middle.checked retained
    have nodeAt : NodeAt (width := width) annotation fuel := by
      intro g s r e p h m c n budget request before value after actual good ready guards
      rcases started : beginNode request before with ⟨handle,action,running⟩
      have same := (beginNode_components request before).1
      rw [started] at same
      have initialGuards : Heap annotation running.checked.native.machine.heap := by rw [same]; exact guards
      cases action with
      | busy | absent => simp only [nodeCall,started] at actual; cases actual
      | ready result => simp only [nodeCall,started] at actual; cases actual; exact initialGuards
      | evaluate owner =>
        obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [nodeCall,started] using actual)
        cases finished
        have current := SourceCurrentOuterPrefixInvariants.activate started good ready
        exact bodyAt body current.1 current.2 initialGuards
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

/-- An actual successful node call retains causal body-to-probe guard profiles. -/
theorem node_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget request before value after}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : NodeReady before request)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap :=
  (all_done annotation fuel).1 actual good ready guards

/-- Every successful body retains the causal heap, including exact Mu cleanup. -/
theorem body_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget request before value after}
    (actual : nodeBody fuel g s r e p h m c n budget request before = .done value after)
    (good : Good (width := width) before) (ready : NodeReady before request)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap :=
  (all_done annotation fuel).2.1 actual good ready guards

/-- Ordered rows retain the causal heap through each returned Parent and descendant call. -/
theorem rows_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget inherited values before result after}
    (actual : rows fuel g s r e p h m c n budget inherited values before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap :=
  (all_done annotation fuel).2.2.1 actual good ready resident guards

/-- A successful inherited prefix and raw rebuild retain the causal heap. -/
theorem descendants_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget inherited value before result after}
    (actual : descendants fuel g s r e p h m c n budget inherited value before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap value)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap :=
  (all_done annotation fuel).2.2.2.1 actual good ready resident guards

/-- Contradictory and live child branches retain the causal guard heap. -/
theorem children_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget inherited values before result after}
    (actual : children fuel g s r e p h m c n budget inherited values before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap :=
  (all_done annotation fuel).2.2.2.2.1 actual good ready available guards

/-- Actual indexed child recursion retains the initial causal guard heap. -/
theorem walk_done (annotation : Guard → Prop) {fuel g s r e p h m c n budget inherited index values before result after}
    (actual : walk fuel g s r e p h m c n budget inherited index values before = .done result after)
    (good : Good (width := width) before) (ready : EqReady before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (guards : Heap annotation before.checked.native.machine.heap) : Heap annotation after.checked.native.machine.heap :=
  (all_done annotation fuel).2.2.2.2.2 actual good ready available guards

private theorem step_heap (annotation : Guard → Prop) {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Step g s r e p h m c n budget first last) (good : Good (caller first)) (inputs : Inputs first)
    (guards : Heap annotation (caller first).checked.native.machine.heap) :
    Heap annotation (caller last).checked.native.machine.heap := by
  cases actual with
  | node_evaluate started =>
    have same := (beginNode_components _ _).1
    rw [started] at same
    rw [same]
    exact guards
  | body_rows | children_walk | walk_head | descendants_children => exact guards
  | rows_edge actual => exact edge_done annotation actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ guards
  | rows_tail first last =>
    have middle := SourceCurrentOuterPrefixInvariants.edge_done first good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩
    exact descendants_done annotation last middle.1 (inputs.1.grows middle.2.1.operations.constraint_growth) middle.2.2
      (edge_done annotation first good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩ guards)
  | walk_tail actual =>
    rename_i fuel before inherited index value result middle rest
    have start := SourceCurrentOuterPrefixInvariants.reached
      (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget)
      (first := .walk (fuel+1) inherited index (value :: rest) before)
      (last := .node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before inherited index).1,value⟩
        (SourceCurrentAllocatedPartialGraph.descend before inherited index).2)
      (.snoc (.refl _) .walk_head) good inputs
    exact node_done annotation actual start.1 start.2 (by exact guards)

/-- Every actual unfinished prefix retains its initial causal guard profiles. -/
theorem reached (annotation : Guard → Prop) {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last) (good : Good (caller first)) (inputs : Inputs first)
    (guards : Heap annotation (caller first).checked.native.machine.heap) :
    Heap annotation (caller last).checked.native.machine.heap := by
  induction actual with
  | refl => exact guards
  | snoc earlier last ih =>
    have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
    exact step_heap annotation last current.1 current.2 ih

/-- An actual busy dispatch retains the initial causal guard heap without assuming completion. -/
theorem busy (annotation : Guard → Prop) {g s r e p h m c n budget handle : Nat} {phase : Phase width} {after : Caller width}
    (good : Good (caller phase)) (inputs : Inputs phase)
    (guards : Heap annotation (caller phase).checked.native.machine.heap)
    (actual : SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget phase = .failed (.nodeMemo handle .busy) after) :
    Heap annotation after.checked.native.machine.heap := by
  obtain ⟨_,fuel,request,past,_⟩ := SourceCurrentOuterPrefixInvariants.busy good inputs actual
  exact reached annotation past good inputs guards

end MicroCFTA.SourceCurrentOuterGuardHeapReturns

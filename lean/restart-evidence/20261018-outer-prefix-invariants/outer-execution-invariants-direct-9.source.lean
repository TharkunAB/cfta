import MicroCFTA.SourceCurrentParentOperationInvariants
import MicroCFTA.SourceCurrentOuterExecutionGrowth
import MicroCFTA.SourceCurrentEqualityOperationFixed
import MicroCFTA.SourceCurrentMuReconstructionEffects

/-!
# Physical invariants along actual outer prefixes

Successful earlier calls derive the physical state used by the next call.
Outer cells retain their captured ready inputs and resident returned values.
No cell asserts a language law for its result. The proof does not exclude
an active key collision or bound fresh recursive requests.
-/
namespace MicroCFTA.SourceCurrentOuterPrefixInvariants
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentLowerOperationInvariants (Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "NativeGood" => SourceCurrentNativeOperationHeap.Good
variable {width : Nat}

/-- An outer node request has an allocated inherited payload and an available value. -/
def NodeReady (before : Caller width) (request : NodeRequest) : Prop :=
  EqReady before.checked.operations.constraints request.inherited ∧
    Available before.checked.native.machine.heap request.value

/-- An outer edge request has an allocated inherited payload and a resident row. -/
def EdgeReady (before : Caller width) (request : EdgeRequest) : Prop :=
  EqReady before.checked.operations.constraints request.inherited ∧
    EdgeResident before.checked.native.machine.heap request.value

private def NodeCell (before : Caller width) (cell : FlatMemoThunk.Cell NodeRequest Node) : Prop :=
  NodeReady before cell.request ∧ ∀ value, cell.status = .returned value → Available before.checked.native.machine.heap value

private def EdgeCell (before : Caller width) (cell : FlatMemoThunk.Cell EdgeRequest Edge) : Prop :=
  EdgeReady before cell.request ∧ ∀ value, cell.status = .returned value → EdgeResident before.checked.native.machine.heap value

/-- Initial outer cells contain ready captured inputs and only resident completed results. -/
structure Good (before : Caller width) : Prop where
  /-- The checked state retains full physical operation invariants. -/
  checked : NativeGood before.checked
  /-- The merge memo retains available originals and completed results. -/
  stored : Stored before.checked.native.machine.heap before.merge
  /-- Stored Mu probes retain their actual root filters. -/
  probes : InternedFreshOrdinaryProbeHeap.Heap before.checked.native.machine.heap
  /-- Node cells retain their full physical requests and results. -/
  nodes : FlatMemoThunk.Valid (fun request key => request.key = key) (NodeCell before) before.nodeResults
  /-- Edge cells retain their full physical requests and results. -/
  edges : FlatMemoThunk.Valid (fun request key => request.key = key) (EdgeCell before) before.edgeResults

/-- Fresh outer result tables need no preexisting cell premise. -/
theorem initial (before : Checked width) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (fourth : SourceCurrentEmptinessMemo.Memo) (good : NativeGood before)
    (stored : Stored before.native.machine.heap memo) (probes : InternedFreshOrdinaryProbeHeap.Heap before.native.machine.heap) :
    Good (SourceCurrentAllocatedPartialState.initial before memo fourth) :=
  ⟨good,stored,probes,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩

private theorem ready_grows {before after : Caller width} (effect : Effect before.checked after.checked)
    {request : NodeRequest} (ready : NodeReady before request) : NodeReady after request :=
  ⟨ready.1.grows effect.operations.constraint_growth,effect.keeps.available _ ready.2⟩

private theorem edge_ready_grows {before after : Caller width} (effect : Effect before.checked after.checked)
    {request : EdgeRequest} (ready : EdgeReady before request) : EdgeReady after request :=
  ⟨ready.1.grows effect.operations.constraint_growth,edge_grows _ _ effect.keeps.growth _ ready.2⟩

private theorem advance_good {before : Caller width} (good : Good before) (checked : Checked width)
    (fourth : SourceCurrentEmptinessMemo.Memo) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (effect : Effect before.checked checked) (stored : Stored checked.native.machine.heap memo)
    (probes : InternedFreshOrdinaryProbeHeap.Heap checked.native.machine.heap) :
    Good (advance before checked fourth memo) := by
  refine ⟨effect.good,stored,probes,?_,?_⟩
  · apply FlatMemoThunk.Valid.map _ _ _ _ good.nodes
    intro cell valid
    exact ⟨ready_grows effect valid.1,fun value returned => effect.keeps.available _ (valid.2 value returned)⟩
  · apply FlatMemoThunk.Valid.map _ _ _ _ good.edges
    intro cell valid
    exact ⟨edge_ready_grows effect valid.1,fun value returned => edge_grows _ _ effect.keeps.growth _ (valid.2 value returned)⟩

private theorem demand_checked (handle : Nat) (state : FlatMemoThunk.State Key Request Result)
    (keyOf : Request → Key → Prop) (ready : Request → Prop) (resident : Result → Prop)
    (valid : FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value) state) :
    FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value)
      (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand,found] using valid
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | evaluating | returned value => simpa only [FlatMemoThunk.demand,found] using valid
      | suspended =>
        simp only [FlatMemoThunk.demand,found]
        exact FlatMemoThunk.setStatus_valid _ _ _ _ _ valid _ found
          ⟨(valid.checked _ _ found).1,by intro value impossible; cases impossible⟩

private theorem begin_node {before : Caller width} (request : NodeRequest) (good : Good before)
    (ready : NodeReady before request) : Good (beginNode request before).2.2 := by
  refine ⟨good.checked,good.stored,good.probes,?_,good.edges⟩
  apply demand_checked
  exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.nodes rfl
    ⟨ready,by intro value impossible; cases impossible⟩

private theorem begin_edge {before : Caller width} (request : EdgeRequest) (good : Good before)
    (ready : EdgeReady before request) : Good (beginEdge request before).2.2 := by
  refine ⟨good.checked,good.stored,good.probes,good.nodes,?_⟩
  apply demand_checked
  exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.edges rfl
    ⟨ready,by intro value impossible; cases impossible⟩

private theorem finish_checked (handle : Nat) (state : FlatMemoThunk.State Key Request Result)
    (keyOf : Request → Key → Prop) (ready : Request → Prop) (resident : Result → Prop)
    (valid : FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value) state)
    (value : Result) (available : resident value) :
    FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value)
      (FlatMemoThunk.finish handle value state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.finish,found] using valid
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | suspended | returned value => simpa only [FlatMemoThunk.finish,found] using valid
      | evaluating =>
        simp only [FlatMemoThunk.finish,found]
        exact FlatMemoThunk.setStatus_valid _ _ _ _ _ valid _ found
          ⟨(valid.checked _ _ found).1,by intro actual same; cases FlatMemoThunk.Status.returned.inj same; exact available⟩

private theorem finish_node {before : Caller width} (handle : Nat) (value : Node) (good : Good before)
    (available : Available before.checked.native.machine.heap value) : Good (finishNode handle value before) :=
  ⟨good.checked,good.stored,good.probes,finish_checked _ _ _ _ _ good.nodes value available,good.edges⟩

private theorem finish_edge {before : Caller width} (handle : Nat) (value : Edge) (good : Good before)
    (available : EdgeResident before.checked.native.machine.heap value) : Good (finishEdge handle value before) :=
  ⟨good.checked,good.stored,good.probes,good.nodes,finish_checked _ _ _ _ _ good.edges value available⟩

private theorem begin_node_owner {before running : Caller width} {request original : NodeRequest}
    {handle : Nat} (good : Good running)
    (started : beginNode request before = (handle,.evaluate original,running)) : NodeReady running original := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.nodeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.evaluate original,running.nodeResults) at observed
  exact (good.nodes.checked _ _ (FlatMemoThunk.demand_evaluate _ _ _ original observed).2).1

private theorem begin_edge_owner {before running : Caller width} {request original : EdgeRequest}
    {handle : Nat} (good : Good running)
    (started : beginEdge request before = (handle,.evaluate original,running)) : EdgeReady running original := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.evaluate original,running.edgeResults) at observed
  exact (good.edges.checked _ _ (FlatMemoThunk.demand_evaluate _ _ _ original observed).2).1

private theorem begin_node_result {before running : Caller width} {request : NodeRequest} {value : Node}
    {handle : Nat} (good : Good running)
    (started : beginNode request before = (handle,.ready value,running)) : Available running.checked.native.machine.heap value := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.nodeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.ready value,running.nodeResults) at observed
  obtain ⟨original,found,same⟩ := FlatMemoThunk.demand_ready_original _ _ value _ observed
  rw [← same] at found
  exact (good.nodes.checked _ _ found).2 value rfl

private theorem begin_edge_result {before running : Caller width} {request : EdgeRequest} {value : Edge}
    {handle : Nat} (good : Good running)
    (started : beginEdge request before = (handle,.ready value,running)) : EdgeResident running.checked.native.machine.heap value := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.ready value,running.edgeResults) at observed
  obtain ⟨original,found,same⟩ := FlatMemoThunk.demand_ready_original _ _ value _ observed
  rw [← same] at found
  exact (good.edges.checked _ _ found).2 value rfl

private theorem checked_operations {before : Checked width} (good : NativeGood before)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (growth : SourceEqualityConstraintMemoAllocation.Grows before.operations operations) :
    Effect before (advancePhysical before ⟨before.native.machine.heap,operations⟩) := by
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before)
      ⟨before.native.machine.heap,operations⟩ :=
    ⟨SourceEqualityRequiredCache.pure_keeps _ good.heap,
      ⟨good.semantic,good.costs,valid,good.fields.grows growth⟩,growth⟩
  exact ⟨good.advance _ effects,effects.keeps,growth⟩

private theorem physical_heap {before : Checked width} (good : NativeGood before) (heap : State Symbol Guard)
    (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap)
    (fields : SourceCurrentConjunctionEquality.Fields before.operations heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) := by
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) ⟨heap,before.operations⟩ :=
    ⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  exact ⟨good.advance _ effects,keeps,effects.grows⟩

private theorem inherited_prefix {before : Caller width} {edge : Edge} {inherited combined : EqValue}
    (good : Good before) (resident : EdgeResident before.checked.native.machine.heap edge)
    (ready : EqReady before.checked.operations.constraints inherited)
    (actual : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined)) :
    Good (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited) ∧
      Effect before.checked (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited).checked ∧
      EqReady (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited).checked.operations.constraints combined := by
  obtain ⟨result,done,valid,known,growth,_⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
    edge.entry.key.constraint inherited before.checked.operations good.checked.operations ready
    (good.checked.fields edge.entry.key edge resident)
  have same : result = combined := Option.some.inj (Except.ok.inj (done.symm.trans actual))
  subst result
  have effect := checked_operations good.checked _ valid growth
  exact ⟨advance_good good _ _ _ effect (good.stored.grows effect.keeps) good.probes,effect,known⟩

private theorem descended {before : Caller width} (good : Good before) (combined : EqValue) (index : Nat)
    (ready : EqReady before.checked.operations.constraints combined) :
    let actual := SourceCurrentAllocatedPartialGraph.descend before combined index
    Good actual.2 ∧ Effect before.checked actual.2.checked ∧ EqReady actual.2.checked.operations.constraints actual.1 := by
  have checked := SourceEqualityConstraintMemoAllocation.descend_correct combined index before.checked.operations
    good.checked.operations ready
  have effect := checked_operations good.checked _ checked.1 checked.2.2.2
  exact ⟨advance_good good _ _ _ effect (good.stored.grows effect.keeps) good.probes,effect,checked.2.1⟩

private theorem row_children {before : Caller width} (good : Good before) {edge : Edge}
    (resident : EdgeResident before.checked.native.machine.heap edge) : Values before.checked.native.machine.heap edge.children :=
  good.checked.heap.semantic.1.normal.facts.cached.edges edge.entry.key edge resident

private theorem raw_edge (edgeEquality : DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard))
    {before : Caller width} (original : Edge) (children : List Node) (good : Good before)
    (resident : EdgeResident before.checked.native.machine.heap original)
    (available : Values before.checked.native.machine.heap children) :
    let actual := @SourceCurrentAllocatedRawRebuild.edge edgeEquality width original children before.checked
    Good (advance before actual.2 before.fourth before.merge) ∧ Effect before.checked actual.2 ∧
      EdgeResident actual.2.native.machine.heap actual.1 := by
  letI := edgeEquality
  have field := good.checked.fields original.entry.key original resident
  have built := SourceEqualityRequiredCache.edge original.entry.key.symbol original.entry.key.constraint
    children before.checked.native.machine.heap good.checked.heap available
  have semantic := SourceEqualityRequiredSemanticCache.edge original.entry.key.symbol original.entry.key.constraint
    children before.checked.native.machine.heap good.checked.semantic available
  have fields := SourceEqualityAnnotationHeap.run (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) _
    (SourceEqualityAnnotationHeap.makeEdge _ original.entry.key.symbol original.entry.key.constraint children field)
    _ good.checked.fields
  have effect := physical_heap good.checked _ built.1 semantic good.checked.costs fields
  exact ⟨advance_good good _ _ _ effect (good.stored.grows effect.keeps) good.probes,effect,built.2.1⟩

private theorem raw_node (edgeEquality : DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard))
    {before : Caller width} (entry : Interned InternedBinderProtocol.NodeKey) (originals rebuilt : List Edge) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (good : Good before)
    (available : Available before.checked.native.machine.heap (.node entry originals depth free))
    (resident : Edges before.checked.native.machine.heap rebuilt) :
    let actual := @SourceCurrentAllocatedRawRebuild.modify edgeEquality width (.node entry originals depth free) originals rebuilt before.checked
    Good (advance before actual.2 before.fourth before.merge) ∧ Effect before.checked actual.2 ∧
      Available actual.2.native.machine.heap actual.1 := by
  letI := edgeEquality
  by_cases same : rebuilt.map (fun edge => edge.entry.identity) = originals.map (fun edge => edge.entry.identity)
  · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
    exact ⟨good,.refl _ good.checked,available⟩
  · have built := SourceCurrentRequiredHeapEffects.node_constructor
      (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) rebuilt _
      good.checked.semantic good.checked.costs good.checked.fields resident
    have effect := physical_heap good.checked _ built.1 built.2.1 built.2.2.1 built.2.2.2.1
    have actual : SourceCurrentAllocatedRawRebuild.modify (.node entry originals depth free) originals rebuilt before.checked =
        ((run (makeNode rebuilt) before.checked.native.machine.heap).1,
          advancePhysical before.checked ⟨(run (makeNode rebuilt) before.checked.native.machine.heap).2,before.checked.operations⟩) := by
      simp only [SourceCurrentAllocatedRawRebuild.modify,SourceEqualityPartialNodeRebuild.modify,same,↓reduceIte]
      rfl
    rw [actual]
    exact ⟨advance_good good _ _ _ effect (good.stored.grows effect.keeps)
      (InternedFreshOrdinaryProbeHeap.preserve _ _ good.probes (InternedShallowHeap.makeNode_noNewMu rebuilt _)),effect,built.2.2.2.2⟩

private theorem bind_done (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

private def ParentFilters [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    [DecidableEq Node] : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : EdgeRequest} {before : Caller width}
    {value : Edge} {checked fourth memo},
    SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge = .done value checked fourth memo →
    Good before → EdgeReady before request → InternedFreshOrdinaryProbeHeap.Heap checked.native.machine.heap

private theorem edge_body [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (filters : ParentFilters (width := width))
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {value : Edge}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done value after)
    (good : Good before) (ready : EdgeReady before request) :
    Good after ∧ Effect before.checked after.checked ∧ EdgeResident after.checked.native.machine.heap value := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed => simp only [edgeBody,observed] at actual; cases actual
  | done result checked fourth memo =>
    simp only [edgeBody,observed] at actual
    cases actual
    have checked := SourceCurrentParentOperationInvariants.parent observed good.checked good.stored
      (fun _ => ⟨good.checked.fields request.value.entry.key request.value ready.2,ready.1,row_children good ready.2⟩)
    exact ⟨advance_good good _ _ _ checked.1 checked.2.1 (filters observed good ready),checked.1,checked.2.2⟩

private theorem edge_call [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (filters : ParentFilters (width := width))
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {value : Edge}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done value after)
    (good : Good before) (ready : EdgeReady before request) :
    Good after ∧ Effect before.checked after.checked ∧ EdgeResident after.checked.native.machine.heap value := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have initial := begin_edge request good ready
  have same := (beginEdge_components request before).1
  rw [started] at initial same
  cases action with
  | busy | absent => simp only [edgeCall,started] at actual; cases actual
  | ready result =>
    simp only [edgeCall,started] at actual
    cases actual
    exact ⟨initial,same.symm ▸ Effect.refl _ good.checked,begin_edge_result initial started⟩
  | evaluate original =>
    obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [edgeCall,started] using actual)
    cases finished
    obtain ⟨final,effect,resident⟩ := edge_body filters body initial (begin_edge_owner initial started)
    exact ⟨finish_edge _ _ final resident,same.symm ▸ effect,resident⟩

private def NodeAt [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeCall fuel g s r e p h m c n budget request before = .done value after → Good (width := width) before → NodeReady before request →
    Good after ∧ Effect before.checked after.checked ∧ Available after.checked.native.machine.heap value
private def BodyAt [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget request before value after},
  nodeBody fuel g s r e p h m c n budget request before = .done value after → Good (width := width) before → NodeReady before request →
    Good after ∧ Effect before.checked after.checked ∧ Available after.checked.native.machine.heap value
private def RowsAt [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  rows fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Good after ∧ Effect before.checked after.checked ∧ Edges after.checked.native.machine.heap result
private def DescendantsAt [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited value before result after},
  descendants fuel g s r e p h m c n budget inherited value before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → EdgeResident before.checked.native.machine.heap value →
    Good after ∧ Effect before.checked after.checked ∧ EdgeResident after.checked.native.machine.heap result
private def ChildrenAt [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited values before result after},
  children fuel g s r e p h m c n budget inherited values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
    Good after ∧ Effect before.checked after.checked ∧ Values after.checked.native.machine.heap result
private def WalkAt [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (fuel : Nat) : Prop := ∀ {g s r e p h m c n budget inherited index values before result after},
  walk fuel g s r e p h m c n budget inherited index values before = .done result after → Good (width := width) before →
    EqReady before.checked.operations.constraints inherited → Values before.checked.native.machine.heap values →
    Good after ∧ Effect before.checked after.checked ∧ Values after.checked.native.machine.heap result

private theorem all_done [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (filters : ParentFilters (width := width)) (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited index values before result after actual good ready available
      cases values with
      | nil => simp only [walk] at actual; cases actual; exact ⟨good,.refl _ good.checked,by intro value impossible; cases impossible⟩
      | cons value values =>
        cases fuel with
        | zero => simp only [walk] at actual; cases actual
        | succ fuel =>
          obtain ⟨head,middle,first,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
          obtain ⟨initial,descent,childReady⟩ := descended good inherited index ready
          obtain ⟨current,headEffect,headAvailable⟩ := (ih fuel (Nat.lt_succ_self _)).1 first initial
            ⟨childReady,descent.keeps.available _ (available _ List.mem_cons_self)⟩
          obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
          cases last
          have total := descent.trans headEffect
          obtain ⟨finalGood,tailEffect,tailAvailable⟩ := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 rest current
            (ready.grows total.operations.constraint_growth)
            (fun child member => total.keeps.available child (available child (List.mem_cons_of_mem _ member)))
          refine ⟨finalGood,total.trans tailEffect,?_⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact tailEffect.keeps.available _ headAvailable
          · exact tailAvailable _ member
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready available
      cases inherited with
      | contradiction =>
        simp only [SourceCurrentAllocatedPartialWorker.children] at actual
        cases actual
        refine ⟨good,.refl _ good.checked,?_⟩
        intro value member
        obtain ⟨original,_,same⟩ := List.mem_map.mp member
        cases same
        exact empty_available _
      | live identity records => exact walkAt (by simpa only [SourceCurrentAllocatedPartialWorker.children] using actual) good ready available
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before result after actual good ready resident
      obtain ⟨combined,prefixDone,_,_,_,_⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
        value.entry.key.constraint inherited before.checked.operations good.checked.operations ready
        (good.checked.fields value.entry.key value resident)
      have start := inherited_prefix good resident ready prefixDone
      obtain ⟨values,middle,first,last⟩ := bind_done _ _
        (by simpa only [descendants,prefixDone] using actual)
      obtain ⟨current,childEffect,known⟩ := childrenAt first start.1 start.2.2
        (fun child member => start.2.1.keeps.available child (row_children good resident child member))
      cases last
      have total := start.2.1.trans childEffect
      have rebuilt := raw_edge inferInstance value values current (edge_grows _ _ total.keeps.growth _ resident) known
      exact ⟨rebuilt.1,total.trans rebuilt.2.1,rebuilt.2.2⟩
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before result after actual good ready resident
      cases values with
      | nil => simp only [rows] at actual; cases actual; exact ⟨good,.refl _ good.checked,by intro value impossible; cases impossible⟩
      | cons value values =>
        cases fuel with
        | zero => simp only [rows] at actual; cases actual
        | succ fuel =>
          obtain ⟨narrowed,middle,first,later⟩ := bind_done _ _ (by simpa only [rows] using actual)
          obtain ⟨current,edgeEffect,known⟩ := edge_call filters first good ⟨ready,resident _ List.mem_cons_self⟩
          obtain ⟨head,afterChildren,childrenDone,last⟩ := bind_done _ _ later
          obtain ⟨next,childEffect,headKnown⟩ := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 childrenDone current
            (ready.grows edgeEffect.operations.constraint_growth) known
          obtain ⟨tail,final,rest,done⟩ := bind_done _ _ last
          cases done
          have total := edgeEffect.trans childEffect
          obtain ⟨finalGood,tailEffect,tailKnown⟩ := (ih fuel (Nat.lt_succ_self _)).2.2.1 rest next
            (ready.grows total.operations.constraint_growth)
            (fun edge member => edge_grows _ _ total.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member)))
          refine ⟨finalGood,total.trans tailEffect,?_⟩
          intro edge member
          rcases List.mem_cons.mp member with rfl | member
          · exact edge_grows _ _ tailEffect.keeps.growth _ headKnown
          · exact tailKnown edge member
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready
      cases request with
      | mk inherited original =>
        cases original with
        | empty | union => simp only [nodeBody] at actual; cases actual; exact ⟨good,.refl _ good.checked,ready.2⟩
        | reference name => simp only [nodeBody] at actual; cases actual
        | mu entry body depth ordinary =>
          have built := SourceCurrentMuReconstructionEffects.node_body fuel g s r e p h m c n budget
            entry body depth ordinary inherited before good.checked good.probes ready.2
          rw [built] at actual
          cases actual
          exact ⟨good,.refl _ good.checked,InternedConstructionProvenance.cleanup_available _ ready.2⟩
        | node entry originals depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
            obtain ⟨rebuilt,middle,first,last⟩ := bind_done _ _ (by simpa only [nodeBody] using actual)
            have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ ready.2.resident
            obtain ⟨current,effect,known⟩ := (ih fuel (Nat.lt_succ_self _)).2.2.1 first good ready.1 resident
            cases last
            have rebuilt := raw_node inferInstance entry originals rebuilt depth free current (effect.keeps.available _ ready.2) known
            exact ⟨rebuilt.1,effect.trans rebuilt.2.1,rebuilt.2.2⟩
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before value after actual good ready
      rcases started : beginNode request before with ⟨handle,action,running⟩
      have initial := begin_node request good ready
      have same := (beginNode_components request before).1
      rw [started] at initial same
      cases action with
      | busy | absent => simp only [nodeCall,started] at actual; cases actual
      | ready result =>
        simp only [nodeCall,started] at actual
        cases actual
        exact ⟨initial,same.symm ▸ Effect.refl _ good.checked,begin_node_result initial started⟩
      | evaluate original =>
        obtain ⟨result,middle,body,finished⟩ := bind_done _ _ (by simpa only [nodeCall,started] using actual)
        cases finished
        obtain ⟨final,effect,known⟩ := bodyAt body initial (begin_node_owner initial started)
        exact ⟨finish_node _ _ final known,same.symm ▸ effect,known⟩
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached Ancestor)
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

/-- Each actual outer phase names its current ready operands. -/
def Inputs (phase : Phase width) : Prop :=
  match phase with
  | .node _ request before | .body _ request before => NodeReady before request
  | .rows _ inherited values before =>
      EqReady before.checked.operations.constraints inherited ∧ Edges before.checked.native.machine.heap values
  | .descendants _ inherited value before =>
      EqReady before.checked.operations.constraints inherited ∧ EdgeResident before.checked.native.machine.heap value
  | .children _ inherited values before | .walk _ inherited _ values before =>
      EqReady before.checked.operations.constraints inherited ∧ Values before.checked.native.machine.heap values

private theorem step_good [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (filters : ParentFilters (width := width))
    {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Step g s r e p h m c n budget first last) (good : Good (caller first)) (inputs : Inputs first) :
    Good (caller last) ∧ Inputs last := by
  cases actual with
  | node_evaluate started =>
    have current := begin_node _ good inputs
    dsimp only [SourceCurrentOuterActiveAncestry.caller] at current
    rw [started] at current
    exact ⟨current,begin_node_owner current started⟩
  | body_rows shaped =>
    refine ⟨good,inputs.1,?_⟩
    have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ inputs.2.resident
    simpa only [shaped,nodeEdges,SourceCurrentOuterActiveAncestry.caller,Edges] using resident
  | rows_edge actual =>
    obtain ⟨current,effect,resident⟩ := edge_call filters actual good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩
    exact ⟨current,inputs.1.grows effect.operations.constraint_growth,resident⟩
  | rows_tail edge children =>
    obtain ⟨current,effect,resident⟩ := edge_call filters edge good ⟨inputs.1,inputs.2 _ List.mem_cons_self⟩
    obtain ⟨final,last,_⟩ := (all_done filters _).2.2.2.1 children current
      (inputs.1.grows effect.operations.constraint_growth) resident
    have total := effect.trans last
    exact ⟨final,inputs.1.grows total.operations.constraint_growth,
      fun row member => edge_grows _ _ total.keeps.growth row (inputs.2 row (List.mem_cons_of_mem _ member))⟩
  | descendants_children actual =>
    have current := inherited_prefix good inputs.2 inputs.1 actual
    exact ⟨current.1,current.2.2,fun child member => current.2.1.keeps.available _ (row_children good inputs.2 child member)⟩
  | children_walk _ => exact ⟨good,inputs⟩
  | walk_head =>
    rename_i fuel combined index value rest before
    have current := descended good combined index inputs.1
    exact ⟨current.1,current.2.2,current.2.1.keeps.available _ (inputs.2 _ List.mem_cons_self)⟩
  | walk_tail actual =>
    have current := descended good _ _ inputs.1
    obtain ⟨final,effect,_⟩ := (all_done filters _).1 actual current.1
      ⟨current.2.2,current.2.1.keeps.available _ (inputs.2 _ List.mem_cons_self)⟩
    have total := current.2.1.trans effect
    exact ⟨final,inputs.1.grows total.operations.constraint_growth,
      fun child member => total.keeps.available _ (inputs.2 child (List.mem_cons_of_mem _ member))⟩

private theorem reached_good [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
    (filters : ParentFilters (width := width))
    {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last) (good : Good (caller first)) (inputs : Inputs first) :
    Good (caller last) ∧ Inputs last := by
  induction actual with
  | refl => exact ⟨good,inputs⟩
  | snoc earlier last ih => exact step_good filters last ih.1 ih.2

end MicroCFTA.SourceCurrentOuterPrefixInvariants

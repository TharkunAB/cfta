import MicroCFTA.SourceCurrentOuterResourceWriters
import MicroCFTA.SourceCurrentResourceParentClosed
import MicroCFTA.MergedColdReaderClosed
import MicroCFTA.InternedFreshProbeKeys

/-!
# Closed inputs through actual outer prefixes

Returned node cells preserve closure for their captured closed inputs.
The actual Parent writer supplies closure for returned edge children.
-/
namespace MicroCFTA.SourceCurrentOuterClosedInputs
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialWorkerStability (bind_done_iff)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

/-- Returned node cells preserve closure of their captured closed inputs. -/
def NodeStored (state : Caller width) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (fun request result => request.value.free = [] → result.free = []))
    state.nodeResults

/-- Each actual phase retains closure of its literal inputs. -/
def InputsClosed (phase : Phase width) : Prop :=
  match phase with
  | .node _ request _ | .body _ request _ => request.value.free = []
  | .rows _ _ values _ => MergedColdReaderClosedInputs.ClosedEdges values
  | .descendants _ _ edge _ => MergedColdReaderClosedInputs.ClosedValues edge.children
  | .children _ _ values _ | .walk _ _ _ values _ => MergedColdReaderClosedInputs.ClosedValues values

theorem initial (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    NodeStored (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  FlatMemoThunk.empty_valid _ _

private theorem same_nodes {before after : Caller width}
    (same : after.nodeResults = before.nodeResults) (stored : NodeStored before) : NodeStored after := by
  simpa only [NodeStored, same] using stored

private theorem begin_stored (request : NodeRequest) {before : Caller width}
    (stored : NodeStored before) : NodeStored (beginNode request before).2.2 := by
  apply FlatMemoThunk.demand_spec
  exact FlatMemoThunk.lookup_valid request.key request before.nodeResults _ _ stored rfl trivial

private theorem finish_stored (handle : Nat) (result : Node) {before : Caller width}
    (stored : NodeStored before) (closed : result.free = []) :
    NodeStored (finishNode handle result before) :=
  FlatMemoThunk.finish_spec handle result before.nodeResults _ _ stored (fun _ _ _ => closed)

variable {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
  (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem reservation [DecidableEq (EdgeKey Symbol Guard)]
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest}
    {before : Caller (bits+2)} {memos : Memos} {profile : Profile} {alphabet : List Guard}
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentParentAlphabetReservation.UniformReserved bits budget alphabet profile) :
    SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile := by
  generalize started : beginEdge request before = observation
  obtain ⟨handle,action,running⟩ := observation
  cases action with
  | evaluate captured =>
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have checked := (beginEdge_components request before).1
      rw [started] at checked
      dsimp only at checked
      have bounded : Fits profile running.checked := by simpa only [checked] using fits
      have carrier : Carrier (fun guard => guard ∈ alphabet) running.checked.native.machine.heap := by simpa only [checked] using known
      have room := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet captured
        running memos runningContext profile bounded carrier owner.inherited owner.input uniform
      simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using room
  | ready | busy | absent => simp only [SourceCurrentEdgeCallNumeric.Reserved,started]

section ClosedHelpers
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem node_hit_closed
    {inventory : Inventory} {request : NodeRequest} {before after : Caller (bits+2)}
    {memos : Memos} {handle : Nat} {result : Node}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .ready result, after))
    (stored : NodeStored before) (closed : request.value.free = []) : result.free = [] := by
  have sameCaller := (SourceCurrentAllocatedPartialMemoSound.beginNode_ready_sound formulas solver request before
    initial.sound initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent
    inherited available handle result after started).1
  subst after
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun observation => (observation.2.1, observation.2.2.nodeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.ready result, before.nodeResults) at observed
  obtain ⟨owner,found,unchanged⟩ := FlatMemoThunk.demand_ready_original _ _ result _ observed
  have publishedStored := FlatMemoThunk.lookup_valid request.key request before.nodeResults
    (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (fun request result => request.value.free = [] → result.free = [])) stored rfl trivial
  obtain ⟨cell,present,key⟩ := publishedStored.linked request.key published.1 (FlatMemoThunk.lookup_stored _ _ _)
  have cells := Option.some.inj (present.symm.trans found)
  subst cell
  have retained : before.nodeResults.cells handle = some ⟨owner, .returned result⟩ := by
    rw [unchanged]
    have handles : published.1 = handle := congrArg Prod.fst started
    simpa only [handles] using found
  have ownerGood := initial.sound.nodes _ _ retained
  have same := InternedFreshProbeKeys.resident_reference_injective before.checked.native.machine.heap
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent owner.value request.value
    ownerGood.input.resident available.resident (congrArg Prod.snd key)
  have conditional := publishedStored.checked _ _ found
  apply conditional
  simpa only [same] using closed

private theorem node_start_closed
    {inventory : Inventory} {request captured : NodeRequest} {before running : Caller (bits+2)}
    {memos : Memos} {handle : Nat}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .evaluate captured, running))
    (closed : request.value.free = []) : captured.value.free = [] := by
  obtain ⟨current,owner,key,_cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
  have checked := (beginNode_components request before).1
  rw [started] at checked
  dsimp only at checked
  have candidate : Available running.checked.native.machine.heap request.value := by simpa only [checked] using available
  have same := InternedFreshProbeKeys.resident_reference_injective running.checked.native.machine.heap
    current.ready.semantic.ready.semantic.1.normal.facts.coherent captured.value request.value
    owner.input.resident candidate.resident (congrArg Prod.snd key)
  simpa only [same] using closed

private theorem modify_closed (original : Node) (oldRows newRows : List Edge)
    (before : SourceEqualityNativeDemand.State (bits+2))
    (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (resident : Edges before.native.machine.heap newRows)
    (closedOriginal : original.free = []) (closedRows : ClosedEdges newRows) :
    (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).1.free = [] := by
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · simpa only [SourceCurrentAllocatedRawRebuild.modify_unchanged original oldRows newRows before same] using closedOriginal
  · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte] using
      MergedColdReaderClosedInputs.makeNode_closed newRows before.native.machine.heap facts resident closedRows

end ClosedHelpers

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {g s r e p h m c n budget : Nat}

private def NodeCallAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {request : NodeRequest} {before after : Caller (bits+2)} {result : Node},
    Reached g s r e p h m c n budget first (.node fuel request before) →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    NodeStored before → request.value.free = [] → NodeStored after ∧ result.free = []

private def NodeBodyAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {request : NodeRequest} {before after : Caller (bits+2)} {result : Node},
    Reached g s r e p h m c n budget first (.body fuel request before) →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    NodeStored before → request.value.free = [] → NodeStored after ∧ result.free = []

private def RowsAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {inherited : SourceEqualityConstraintAllocation.Value} {values results : List Edge} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.rows fuel inherited values before) →
    rows fuel g s r e p h m c n budget inherited values before = .done results after →
    NodeStored before → ClosedEdges values → NodeStored after ∧ ClosedEdges results

private def DescendantsAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {inherited : SourceEqualityConstraintAllocation.Value} {value result : Edge} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.descendants fuel inherited value before) →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    NodeStored before → ClosedValues value.children → NodeStored after ∧ ClosedValues result.children

private def ChildrenAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {combined : SourceEqualityConstraintAllocation.Value} {values results : List Node} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.children fuel combined values before) →
    SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n budget combined values before = .done results after →
    NodeStored before → ClosedValues values → NodeStored after ∧ ClosedValues results

private def WalkAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {combined : SourceEqualityConstraintAllocation.Value} {index : Nat} {values results : List Node} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.walk fuel combined index values before) →
    walk fuel g s r e p h m c n budget combined index values before = .done results after →
    NodeStored before → ClosedValues values → NodeStored after ∧ ClosedValues results

namespace Schedule
export SourceCurrentOuterInitialSchedule (parent node body rows descendants children walk parent_reserved rows_ge descendants_ge rebuild_ge)
end Schedule

theorem reached
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget : Nat} {first last : Phase (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (actual : Reached g s r e p h m c n budget first last)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))
    (stored : NodeStored (caller first)) (closed : InputsClosed first) :
    NodeStored (caller last) ∧ InputsClosed last := by
  have resources {phase} (cut : Reached g s r e p h m c n budget first phase) :=
    SourceCurrentOuterPrefixNativeStores.reached formulas solver seed cut initial frame fits known inputs room normal supported causal merged positiveMemo
  have ledger {phase} (cut : Reached g s r e p h m c n budget first phase) :=
    SourceCurrentOuterResourceWriters.reached formulas solver seed cut initial frame fits known inputs room normal supported causal merged positiveMemo origins
  have edgeAt {fuel inherited original rest before narrowed middle}
      (cut : Reached g s r e p h m c n budget first (.rows (fuel+1) inherited (original::rest) before))
      (done : edgeCall fuel g s r e p h m c n budget ⟨inherited,original⟩ before = .done narrowed middle)
      (stored : NodeStored before) (closed : ClosedValues original.children) : NodeStored middle ∧ ClosedValues narrowed.children := by
    obtain ⟨i,globals,current,_,post,frm,fts,carrier,ins,_,_,rm,_,_,_,sup,⟨his⟩,mer,pos,norm⟩ := resources cut
    change Room bits (Schedule.rows (fuel+1) budget current).2 at rm
    rw [Schedule.rows] at rm
    have parentRoom := rm.mono ((Schedule.descendants_ge fuel budget (Schedule.parent budget current)).1.trans
      (Schedule.rows_ge fuel budget (Schedule.descendants fuel budget (Schedule.parent budget current))).1)
    have uniform := Schedule.parent_reserved bits budget current parentRoom
    have reserved := reservation formulas solver (request := ⟨inherited,original⟩) post.context fts carrier ins.1 (ins.2 _ List.mem_cons_self) uniform
    obtain ⟨ni,nm,receipt,_fits,_known⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call formulas solver i budget current.1
      ⟨inherited,original⟩ before globals post.context frm current.2 fts carrier ins.1 (ins.2 _ List.mem_cons_self) uniform done
    have written := SourceCurrentResourceParentWriters.edge_call formulas solver i current.2 globals done post.context frm fts
      ins.1 (ins.2 _ List.mem_cons_self) reserved (ledger cut) norm sup his mer pos
    exact ⟨same_nodes receipt.semantic.nodes stored,SourceCurrentResourceParentClosed.children formulas solver written.2 closed⟩
  have complete : ∀ fuel, NodeCallAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel ∧ NodeBodyAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel ∧ RowsAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel ∧
      DescendantsAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel ∧ ChildrenAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel ∧ WalkAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      have walks : WalkAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel := by
        intro combined index values results before after cut done stored closed
        cases values with
        | nil =>
          simp only [walk] at done
          cases done
          exact ⟨stored,fun _ member => nomatch member⟩
        | cons value rest =>
          cases fuel with
          | zero => simp only [walk] at done; cases done
          | succ fuel =>
            simp only [walk] at done
            obtain ⟨headValue,middle,head,remaining⟩ := (bind_done_iff _ _ _ _).mp done
            obtain ⟨tailValues,finalState,tail,last⟩ := (bind_done_iff _ _ _ _).mp remaining
            cases last
            have headClosed := (ih fuel (Nat.lt_succ_self _)).1 (.snoc cut .walk_head) head stored (closed _ List.mem_cons_self)
            have tailClosed := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 (.snoc cut (.walk_tail head)) tail headClosed.1 (fun _ member => closed _ (List.mem_cons_of_mem _ member))
            refine ⟨tailClosed.1,?_⟩
            intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact headClosed.2
            · exact tailClosed.2 _ member
      have kids : ChildrenAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel := by
        intro combined values results before after cut done stored closed
        cases combined with
        | contradiction =>
          simp only [SourceCurrentAllocatedPartialWorker.children] at done
          cases done
          refine ⟨stored,?_⟩
          intro child member
          obtain ⟨_,_,same⟩ := List.mem_map.mp member
          subst child
          rfl
        | live identity records =>
          exact walks (.snoc cut (.children_walk (by intro same; cases same))) (by simpa only [SourceCurrentAllocatedPartialWorker.children] using done) stored closed
      have desc : DescendantsAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel := by
        intro inherited value result before after cut done stored closed
        cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
        | mk answer operations =>
          cases answer with
          | error message => simp only [descendants,observed] at done; cases done
          | ok answer =>
            cases answer with
            | none => simp only [descendants,observed] at done; cases done
            | some combined =>
              have prefixSame : prefixState before value inherited = advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨before.checked.native.machine.heap,operations⟩) before.fourth before.merge := by simp only [prefixState,SourceCurrentAllocatedInheritedPrefix.state,observed]
              simp only [descendants,observed] at done
              rw [←prefixSame] at done
              obtain ⟨values,middle,run,last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              have equation : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined) := by rw [observed]
              have childCut := Reached.snoc cut (.descendants_children equation)
              have returned := kids childCut run stored closed
              obtain ⟨i,globals,current,_,post,frm,fts,carrier,ins,_,_,rm,_⟩ := resources childCut
              obtain ⟨ni,nm,_graph,_reads,childPost,_frame,_fits,_known,available,_law⟩ := SourceCurrentOuterInitialActual.children formulas solver fuel current post.context frm fts carrier ins.1 ins.2 rm run
              have childrenSame := InternedShallowValues.makeEdge_children value.entry.key.symbol value.entry.key.constraint values middle.checked.native.machine.heap
                childPost.context.ready.semantic.ready.semantic.1.normal.facts.coherent childPost.context.ready.semantic.ready.semantic.1.normal.facts.cached available
              exact ⟨returned.1,by simpa only [SourceCurrentAllocatedRawRebuild.edge,childrenSame] using returned.2⟩
      have rowCalls : RowsAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel := by
        intro inherited values results before after cut done stored closed
        cases values with
        | nil =>
          simp only [rows] at done
          cases done
          exact ⟨stored,fun _ member => nomatch member⟩
        | cons original rest =>
          cases fuel with
          | zero => simp only [rows] at done; cases done
          | succ fuel =>
            simp only [rows] at done
            obtain ⟨narrowed,middle,head,remaining⟩ := (bind_done_iff _ _ _ _).mp done
            obtain ⟨edgeResult,current,children,remaining⟩ := (bind_done_iff _ _ _ _).mp remaining
            obtain ⟨restResults,finalState,tail,last⟩ := (bind_done_iff _ _ _ _).mp remaining
            cases last
            have headClosed := edgeAt cut head stored (closed _ List.mem_cons_self)
            have childClosed := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 (.snoc cut (.rows_edge head)) children headClosed.1 headClosed.2
            have tailClosed := (ih fuel (Nat.lt_succ_self _)).2.2.1 (.snoc cut (.rows_tail head children)) tail childClosed.1 (fun _ member => closed _ (List.mem_cons_of_mem _ member))
            refine ⟨tailClosed.1,?_⟩
            intro edge member
            rcases List.mem_cons.mp member with rfl | member
            · exact childClosed.2
            · exact tailClosed.2 _ member
      have bodies : NodeBodyAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel := by
        intro request before after result cut done stored closed
        obtain ⟨i,globals,current,_,post,frm,fts,carrier,ins,_,_,rm,_⟩ := resources cut
        cases request with
        | mk inherited value =>
          cases value with
          | empty =>
            simp only [nodeBody] at done
            cases done
            exact ⟨stored,rfl⟩
          | union entry members depth free =>
            simp only [nodeBody] at done
            cases done
            exact ⟨stored,closed⟩
          | reference name => simp only [nodeBody] at done; cases done
          | mu entry body depth ordinary =>
            have rebuilt := SourceCurrentAllocatedMuRebuild.resident_rebuild before.checked post.context.ready post.context.probes entry body depth ordinary ins.2
            simp only [nodeBody,rebuilt.1] at done
            cases done
            exact ⟨stored,rebuilt.2.2.1.trans closed⟩
          | node entry original depth free =>
            cases fuel with
            | zero => simp only [nodeBody] at done; cases done
            | succ fuel =>
              simp only [nodeBody] at done
              obtain ⟨results,middle,run,last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              have originals := MergedColdReaderClosed.node_children_closed before.checked.native.machine.heap post.context.ready.semantic.ready.semantic.1.normal.facts entry original depth free ins.2 closed
              have returned := (ih fuel (Nat.lt_succ_self _)).2.2.1 (.snoc cut (.body_rows rfl)) run stored originals
              rw [SourceCurrentOuterInitialPrefix.forecast,Schedule.body] at rm
              have rowRoom := rm.mono (Schedule.rebuild_ge (Schedule.rows fuel budget current)).1
              have edges := InternedEdgeResidency.resident_edges _ post.context.ready.semantic.ready.semantic.1.normal.facts.linked _ ins.2.resident
              obtain ⟨ni,nm,_graph,_reads,rowPost,_frame,_fits,_known,resident,_law⟩ := SourceCurrentOuterInitialActual.rows formulas solver fuel current post.context frm fts carrier ins.1 edges rowRoom run
              exact ⟨returned.1,modify_closed _ _ _ _ rowPost.context.ready.semantic.ready.semantic.1.normal.facts resident closed returned.2⟩
      have nodes : NodeCallAt (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n) (budget := budget) first fuel := by
        intro request before after result cut done stored closed
        obtain ⟨i,globals,current,_,post,_frm,_fts,_known,ins,_⟩ := resources cut
        rcases started : beginNode request before with ⟨handle,action,running⟩
        have runningStored := begin_stored request stored
        rw [started] at runningStored
        cases action with
        | ready value =>
          simp only [nodeCall,started] at done
          cases done
          exact ⟨runningStored,node_hit_closed formulas solver post.context ins.1 ins.2 started stored closed⟩
        | busy | absent => simp only [nodeCall,started] at done; cases done
        | evaluate captured =>
          simp only [nodeCall,started] at done
          obtain ⟨value,middle,body,last⟩ := (bind_done_iff _ _ _ _).mp done
          cases last
          have returned := bodies (.snoc cut (.node_evaluate started)) body runningStored (node_start_closed formulas solver post.context ins.1 ins.2 started closed)
          exact ⟨finish_stored handle result returned.1 returned.2,returned.2⟩
      exact ⟨nodes,bodies,rowCalls,desc,kids,walks⟩
  induction actual with
  | refl => exact ⟨stored,closed⟩
  | snoc earlier step ih =>
    obtain ⟨stored,closed⟩ := ih
    cases step with
    | @node_evaluate request before handle running original fuel started =>
      obtain ⟨i,globals,current,_,post,_frm,_fts,_known,ins,_⟩ := resources earlier
      have retained := begin_stored request stored
      rw [started] at retained
      exact ⟨retained,node_start_closed formulas solver post.context ins.1 ins.2 started closed⟩
    | body_rows shape =>
      obtain ⟨i,globals,current,_,post,_frm,_fts,_known,ins,_⟩ := resources earlier
      dsimp only [InputsClosed,SourceCurrentOuterPrefixInvariants.Inputs,SourceCurrentOuterPrefixInvariants.NodeReady] at closed ins
      rw [shape] at closed ins
      exact ⟨stored,MergedColdReaderClosed.node_children_closed _ post.context.ready.semantic.ready.semantic.1.normal.facts _ _ _ _ ins.2 closed⟩
    | rows_edge done => exact edgeAt earlier done stored (closed _ List.mem_cons_self)
    | rows_tail edge children =>
      have head := edgeAt earlier edge stored (closed _ List.mem_cons_self)
      have returned := (complete _).2.2.2.1 (.snoc earlier (.rows_edge edge)) children head.1 head.2
      exact ⟨returned.1,fun _ member => closed _ (List.mem_cons_of_mem _ member)⟩
    | descendants_children => exact ⟨stored,closed⟩
    | children_walk => exact ⟨stored,closed⟩
    | walk_head => exact ⟨stored,closed _ List.mem_cons_self⟩
    | walk_tail done =>
      have returned := (complete _).1 (.snoc earlier .walk_head) done stored (closed _ List.mem_cons_self)
      exact ⟨returned.1,fun _ member => closed _ (List.mem_cons_of_mem _ member)⟩

end MicroCFTA.SourceCurrentOuterClosedInputs

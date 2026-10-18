import MicroCFTA.SourceCurrentOuterEdgeIdleReached
import MicroCFTA.SourceCurrentOuterEdgeMemoFailure
import MicroCFTA.SourceCurrentOuterInitialPrefix

/-!
# Initial outer facts exclude edge memo diagnostics

An idle edge table cannot report a busy edge. Valid key links also exclude
an absent edge cell. An actual edge memo fault supplies its own reached
row entry, whose semantic context and idle edge table follow from initial
facts. Node memo collisions remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentOuterInitialEdgeMemoFailure
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterPrefixInvariants (Inputs)
open SourceCurrentOuterEdgeIdle (EdgeIdle)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "forecast" => SourceCurrentOuterInitialPrefix.forecast

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem not_absent (request : EdgeRequest) (before : Caller width) (valid : Valid before) :
    (beginEdge request before).2.1 ≠ .absent := by
  cases published : before.edgeResults.table request.key with
  | none => simp only [beginEdge, FlatMemoThunk.lookupOrInsert, published, FlatMemoThunk.demand, put]; simp
  | some handle =>
    obtain ⟨⟨original,status⟩,present,_key⟩ := valid.edges.linked request.key handle published
    cases status <;> simp only [beginEdge,FlatMemoThunk.lookupOrInsert,published,FlatMemoThunk.demand,present] <;> simp

variable [DecidableEq Symbol] [DecidableEq Node]

/-- Valid links and an idle edge table exclude every local edge memo observation. -/
theorem edge_no_memo_failure (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) (valid : Valid before) (idle : EdgeIdle before)
    (handle : Nat) (observation : FlatMemoThunk.Observation EdgeRequest Edge) (after : Caller width) :
    SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget request before ≠
      .failed (.edgeMemo handle observation) after := by
  intro failed
  rcases started : beginEdge request before with ⟨selected,phase,running⟩
  cases phase with
  | ready value =>
    simp only [SourceCurrentAllocatedPartialWorker.edgeCall,started] at failed
    cases failed
  | evaluate original =>
    simp only [SourceCurrentAllocatedPartialWorker.edgeCall,started,
      SourceCurrentAllocatedPartialWorker.edgeBody] at failed
    split at failed <;> simp only [SourceCurrentAllocatedPartialWorker.Outcome.bind] at failed <;> cases failed
  | busy =>
    have safe := SourceCurrentOuterEdgeIdle.edge_call fuel g s r e p h m c n budget request before idle
    simp only [SourceCurrentAllocatedPartialWorker.edgeCall,started] at failed
    cases failed
    simpa only [SourceCurrentAllocatedPartialWorker.edgeCall,started,SourceCurrentOuterEdgeIdle.Safe,
      SourceCurrentOuterEdgeIdle.NoEdgeBusy] using safe
  | absent =>
    exact not_absent request before valid (congrArg (fun result => result.2.1) started)

variable {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Initial semantics, scheduled capacity and edge idle exclude every edge memo fault in all outer phases. -/
theorem no_edge_memo_failure {g s r e p h m c n budget : Nat} {phase : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller phase) memos)
    (frame : Frame formulas solver inventory (caller phase).checked)
    (fits : Fits seed.2 (caller phase).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) (caller phase).checked.native.machine.heap)
    (inputs : Inputs phase) (room : Room bits (forecast budget phase seed).2)
    (idle : EdgeIdle (caller phase)) (handle : Nat)
    (observation : FlatMemoThunk.Observation EdgeRequest Edge) (after : Caller (bits+2)) :
    SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget phase ≠
      .failed (.edgeMemo handle observation) after := by
  intro failed
  obtain ⟨fuel,inherited,original,rest,before,actual,edgeFailed⟩ := SourceCurrentOuterEdgeMemoFailure.failed failed
  obtain ⟨_next,_final,_current,_trace,post,_frame,_fits,_carrier,_ready,_below,_subset,_room,_numeric,_known,_need⟩ :=
    SourceCurrentOuterInitialPrefix.reached formulas solver seed actual initial frame fits known inputs room
  have currentIdle := SourceCurrentOuterEdgeIdleReached.reached actual idle
  exact edge_no_memo_failure fuel g s r e p h m c n budget ⟨inherited,original⟩ before
    post.context.sound.valid currentIdle handle observation after edgeFailed

end MicroCFTA.SourceCurrentOuterInitialEdgeMemoFailure

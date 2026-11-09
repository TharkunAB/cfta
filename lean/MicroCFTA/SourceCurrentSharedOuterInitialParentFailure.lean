import MicroCFTA.SourceCurrentSharedOuterParentFailure
import MicroCFTA.SourceCurrentSharedOuterEdgeParentFailure
import MicroCFTA.SourceCurrentSharedOuterInitialPrefix

/-!
# Initial bounds exclude Parent faults in all outer phases

A literal Parent fault supplies its own reached row entry. The prefix
proof derives that entry's context, ready inputs and resource seed.
The initial scheduled capacity and nine fuel bounds then exclude the fault.
The proof retains the actual shared fault and its row entry. Outer fuel
exhaustion and outer memo faults remain separate outcomes.
-/
namespace MicroCFTA.SourceCurrentSharedOuterInitialParentFailure
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentSharedOuterPrefixInvariants (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentSharedOuterExecutionAncestry.caller
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
namespace Schedule
export SourceCurrentSharedOuterInitialSchedule (parent rows descendants rows_ge descendants_ge parent_reserved)
end Schedule

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Initial scheduled capacity and lower fuels exclude every Parent diagnostic at any outer outcome. -/
theorem no_parent_failure {g s r e p h m c n budget : Nat} {phase : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller phase) memos)
    (frame : Frame formulas solver inventory (caller phase).checked)
    (fits : Fits seed.2 (caller phase).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) (caller phase).checked.native.machine.heap)
    (inputs : Inputs phase) (room : Room bits (forecast budget phase seed).2)
    (gBound : phaseNeed budget phase seed ≤ g) (sBound : phaseNeed budget phase seed ≤ s)
    (rBound : phaseNeed budget phase seed ≤ r) (eBound : phaseNeed budget phase seed ≤ e)
    (pBound : phaseNeed budget phase seed ≤ p) (hBound : phaseNeed budget phase seed ≤ h)
    (mBound : phaseNeed budget phase seed ≤ m) (cBound : phaseNeed budget phase seed ≤ c)
    (nBound : phaseNeed budget phase seed ≤ n)
    (observation : SourceCurrentAllocatedSharedParentWorker.Fault (bits+2)) (after : Caller (bits+2)) :
    SourceCurrentSharedOuterActiveAncestry.run g s r e p h m c n budget phase ≠ .failed (.parent observation) after := by
  intro failed
  obtain ⟨fuel,inherited,original,rest,before,actual,edgeFailed⟩ := SourceCurrentSharedOuterParentFailure.failed failed
  obtain ⟨_next,_final,current,_trace,post,returned,numeric,carrier,ready,_below,_subset,currentRoom,_fits,_carrier,need⟩ :=
    SourceCurrentSharedOuterInitialPrefix.reached formulas solver seed actual initial frame fits known inputs room
  have parentRoom : Room bits (Schedule.parent budget current).2 := by
    simp only [SourceCurrentSharedOuterInitialPrefix.forecast, Schedule.rows] at currentRoom
    exact currentRoom.mono ((Schedule.descendants_ge fuel budget (Schedule.parent budget current)).1.trans
      (Schedule.rows_ge fuel budget (Schedule.descendants fuel budget (Schedule.parent budget current))).1)
  have parentNeed : SourceCurrentSharedParentUniformEnvelope.fuel budget current.1 current.2 ≤ phaseNeed budget phase seed :=
    Nat.le_trans (SourceCurrentSharedOuterInitialFuel.rows_parent_le fuel budget current) need
  exact SourceCurrentSharedOuterEdgeParentFailure.edge_no_parent_failure formulas solver
    _ budget current.1 ⟨inherited,original⟩ before _ post.context returned current.2 numeric carrier
    ready.1 (ready.2 original List.mem_cons_self) (Schedule.parent_reserved bits budget current parentRoom)
    fuel g s r e p h m c n
    (Nat.le_trans parentNeed gBound) (Nat.le_trans parentNeed sBound) (Nat.le_trans parentNeed rBound)
    (Nat.le_trans parentNeed eBound) (Nat.le_trans parentNeed pBound) (Nat.le_trans parentNeed hBound)
    (Nat.le_trans parentNeed mBound) (Nat.le_trans parentNeed cBound) (Nat.le_trans parentNeed nBound)
    observation after edgeFailed

end MicroCFTA.SourceCurrentSharedOuterInitialParentFailure

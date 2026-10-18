import MicroCFTA.SourceCurrentOuterParentFailure
import MicroCFTA.SourceCurrentOuterEdgeParentFailure
import MicroCFTA.SourceCurrentOuterInitialPrefix

/-!
# Initial bounds exclude Parent faults in all outer phases

A literal Parent fault supplies its own reached row entry. The prefix
theorem derives that entry's context, ready inputs and resource seed.
The initial scheduled capacity and nine fuel bounds then exclude the fault.
Outer fuel exhaustion and outer memo faults remain separate outcomes.
-/
namespace MicroCFTA.SourceCurrentOuterInitialParentFailure
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterPrefixInvariants (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "forecast" => SourceCurrentOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentOuterInitialFuel.phaseNeed
namespace Schedule
export SourceCurrentOuterInitialSchedule (parent rows descendants rows_ge descendants_ge parent_reserved)
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
    (observation : SourceCurrentAllocatedParentWorker.Fault (bits+2)) (after : Caller (bits+2)) :
    SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget phase ≠ .failed (.parent observation) after := by
  intro failed
  obtain ⟨fuel,inherited,original,rest,before,actual,edgeFailed⟩ := SourceCurrentOuterParentFailure.failed failed
  obtain ⟨_next,_final,current,_trace,post,returned,numeric,carrier,ready,_below,_subset,currentRoom,_fits,_carrier,need⟩ :=
    SourceCurrentOuterInitialPrefix.reached formulas solver seed actual initial frame fits known inputs room
  have parentRoom : Room bits (Schedule.parent budget current).2 := by
    change Room bits (Schedule.rows fuel budget (Schedule.descendants fuel budget (Schedule.parent budget current))).2 at currentRoom
    exact currentRoom.mono ((Schedule.descendants_ge fuel budget (Schedule.parent budget current)).1.trans
      (Schedule.rows_ge fuel budget (Schedule.descendants fuel budget (Schedule.parent budget current))).1)
  have parentNeed : SourceCurrentParentUniformEnvelope.fuel budget current.1 current.2 ≤ phaseNeed budget phase seed :=
    (SourceCurrentOuterInitialFuel.rows_parent_le fuel budget current).trans need
  exact SourceCurrentOuterEdgeParentFailure.edge_no_parent_failure formulas solver
    _ budget current.1 ⟨inherited,original⟩ before _ post.context returned current.2 numeric carrier
    ready.1 (ready.2 original List.mem_cons_self) (Schedule.parent_reserved bits budget current parentRoom)
    fuel g s r e p h m c n
    (parentNeed.trans gBound) (parentNeed.trans sBound) (parentNeed.trans rBound)
    (parentNeed.trans eBound) (parentNeed.trans pBound) (parentNeed.trans hBound)
    (parentNeed.trans mBound) (parentNeed.trans cBound) (parentNeed.trans nBound)
    observation after edgeFailed

end MicroCFTA.SourceCurrentOuterInitialParentFailure

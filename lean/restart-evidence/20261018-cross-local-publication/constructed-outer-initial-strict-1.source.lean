import MicroCFTA.SourceCurrentOuterInitialActual
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

/-!
# Outer entry from an actual closed source construction

Closed source execution derives its guard heap. An empty native cache uses
that heap to derive its initial Frame. A completed bounded outer node call
then has the existing language law without a supplied guard certificate.
Caller context, numeric resources and successful execution remain explicit.
-/
namespace MicroCFTA.SourceCurrentConstructedOuterInitial
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceRecursiveIntersectionKernel (Machine)
open SourceEqualityNativeDemand (initial)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialWorker (nodeCall)

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual closed construction derives the guard premise of an initial native Frame. -/
theorem frame (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (expression : Syntax Symbol Guard) (root : Node)
    (constructed : build expression [] empty = .done root machine.heap)
    (ready : SourceCurrentConjunctionClassScan.Ready (⟨initial width machine,operations⟩ : Checked width))
    (same : inventory.source = machine.heap) :
    Frame formulas solver inventory (⟨initial width machine,operations⟩ : Checked width) := by
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap := by
    simpa only [constructed,Outcome.state] using
      SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
  exact Frame.initial formulas solver inventory machine operations ready guards same

/-- A completed constructed-source node call needs no separate initial guard heap or Frame. -/
theorem node_call [DecidableEq Symbol] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (expression : Syntax Symbol Guard) (root : Node)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (constructed : build expression [] empty = .done root machine.heap)
    (before after : Caller (bits+2)) (inventory : Inventory) (memos : EndpointMemoGateTrace.Memos)
    (entry : before.checked = (⟨initial (bits+2) machine,operations⟩ : Checked (bits+2)))
    (same : inventory.source = machine.heap)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (seed : Seed) (fits : Fits seed.2 before.checked)
    (carrier : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (request : NodeRequest) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (fuel g s r e p h m c n budget : Nat)
    (room : Room bits (SourceCurrentOuterInitialActual.Schedule.node fuel budget seed).2)
    (result : Node)
    (called : nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  have initialReady : SourceCurrentConjunctionClassScan.Ready
      (⟨initial (bits+2) machine,operations⟩ : Checked (bits+2)) := entry ▸ context.ready
  have initialFrame := frame formulas solver inventory machine operations expression root constructed initialReady same
  have currentFrame : Frame formulas solver inventory before.checked := entry.symm ▸ initialFrame
  obtain ⟨_next,_final,_actual,_reads,_post,_frame,_fits,_carrier,resultAvailable,law⟩ :=
    SourceCurrentOuterInitialActual.node_call formulas solver fuel seed context currentFrame fits carrier
      inherited available room called
  exact ⟨resultAvailable,law⟩

end MicroCFTA.SourceCurrentConstructedOuterInitial

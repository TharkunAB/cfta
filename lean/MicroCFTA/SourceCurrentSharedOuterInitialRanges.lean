import MicroCFTA.SourceCurrentSharedOuterInitialPrefix
import MicroCFTA.SourceCurrentAllocatedSharedPartialChecks
import MicroCFTA.SourceCurrentAllocatedSharedPartialCallSteps

/-!
# Initial resources at reached shared Parent entries

One initial scheduled Room supplies ranges at every supplied literal row
prefix. Edge demand retains the checked state and captures its actual owner.
That owner's current Context and uniform reservation derive its range plan
before the edge or Parent outcome is known.

The phase relation has six cases. This proof uses its actual row entry.
It requires no whole-call success and covers a Parent that later fails.
It does not extract every runtime fault prefix or derive graph-wide Checks.
-/
namespace MicroCFTA.SourceCurrentSharedOuterInitialRanges
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentSharedOuterExecutionAncestry (Reached)
open SourceCurrentSharedOuterPrefixInvariants (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
local notation "caller" => SourceCurrentSharedOuterExecutionAncestry.caller
namespace Schedule
export SourceCurrentSharedOuterInitialSchedule (parent rows descendants parent_reserved rows_ge descendants_ge)
end Schedule
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
variable {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem edge_ranges {budget : Nat} {request : EdgeRequest} {before : Caller (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (room : Room bits (Schedule.parent budget seed).2) :
    SourceCurrentAllocatedSharedPartialChecks.CallRanges budget request before := by
  intro handle original running started
  obtain ⟨current, owner, _key, _cell⟩ := SourceCurrentAllocatedSharedPartialCallSteps.edge_start
    formulas solver initial inherited resident started
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, _merge, _fourth, _nodes⟩ := components
  exact SourceCurrentSharedParentUniformRanges.resident_ranges formulas solver inventory budget seed.1
    original running memos current (by simpa only [checked] using frame) seed.2
    (by simpa only [checked] using fits) (by simpa only [checked] using known)
    owner.inherited owner.input (Schedule.parent_reserved bits budget seed room)

/-- Every supplied literal row prefix derives ranges for its exact evaluated edge owner. -/
theorem rows_call_ranges {g s r e p h m c n budget fuel : Nat}
    {first : Phase (bits + 2)} {inherited : EqValue} {original : Edge} {rest : List Edge}
    {before : Caller (bits + 2)} {inventory : Inventory} {memos : Memos} (seed : Seed)
    (actual : Reached g s r e p h m c n budget first (.rows (fuel + 1) inherited (original :: rest) before))
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (SourceCurrentSharedOuterInitialPrefix.forecast budget first seed).2) :
    SourceCurrentAllocatedSharedPartialChecks.CallRanges budget ⟨inherited, original⟩ before := by
  obtain ⟨next, final, current, _trace, post, returned, numeric, carrier, operands,
      _below, _subset, currentRoom, _remaining⟩ :=
    SourceCurrentSharedOuterInitialPrefix.reached formulas solver seed actual initial frame fits known inputs room
  simp only [SourceCurrentSharedOuterInitialPrefix.forecast, Schedule.rows] at currentRoom
  have parentRoom : Room bits (Schedule.parent budget current).2 := currentRoom.mono
    ((Schedule.descendants_ge fuel budget (Schedule.parent budget current)).1.trans
      (Schedule.rows_ge fuel budget (Schedule.descendants fuel budget (Schedule.parent budget current))).1)
  exact edge_ranges formulas solver current post.context returned numeric carrier operands.1
    (operands.2 original List.mem_cons_self) parentRoom

end MicroCFTA.SourceCurrentSharedOuterInitialRanges

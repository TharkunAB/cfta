import MicroCFTA.SourceCurrentOuterInitialPrefix
import MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges
import MicroCFTA.SourceCurrentParentUniformRanges

/-!
# Initial forecasts supply actual outer worker ranges

The proof follows literal unfinished prefixes. A successful earlier call
supplies only its exact continuation state. The initial forecast supplies
the room for every reached Parent call. Failed calls need no continuation.
The theorem does not prove completion or derive the initial machine room.
-/
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.SourceCurrentOuterInitialWorkerRanges
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentOuterPrefixInvariants (Inputs)
namespace Ranges
export SourceCurrentAllocatedPartialWorkerRanges
  (After nodeCall nodeBody edgeCall edgeBody rows descendants children walk)
end Ranges
namespace Schedule
export SourceCurrentOuterInitialSchedule
  (parent node rows descendants parent_reserved descendants_ge rows_ge)
end Schedule
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

private def phaseRank : Phase width → Nat
  | .node fuel .. => 4 * fuel + 3
  | .body fuel .. | .rows fuel .. | .descendants fuel .. => 4 * fuel + 2
  | .children fuel .. => 4 * fuel + 1
  | .walk fuel .. => 4 * fuel

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private noncomputable def phaseRanges (g s r e p h m c n budget : Nat) : Phase (bits + 2) → Prop
  | .node fuel request before => Ranges.nodeCall fuel g s r e p h m c n budget request before
  | .body fuel request before => Ranges.nodeBody fuel g s r e p h m c n budget request before
  | .rows fuel inherited values before => Ranges.rows fuel g s r e p h m c n budget inherited values before
  | .descendants fuel inherited edge before => Ranges.descendants fuel g s r e p h m c n budget inherited edge before
  | .children fuel combined values before => Ranges.children fuel g s r e p h m c n budget combined values before
  | .walk fuel combined index values before => Ranges.walk fuel g s r e p h m c n budget combined index values before

private theorem edge_ranges {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before : Caller (bits + 2)} {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (room : Room bits (Schedule.parent budget seed).2) :
    Ranges.edgeCall fuel g s r e p h m c n budget request before := by
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  cases action with
  | ready result => simp only [Ranges.edgeCall, started]
  | busy => simp only [Ranges.edgeCall, started]
  | absent => simp only [Ranges.edgeCall, started]
  | evaluate original =>
      obtain ⟨current, owner, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start
        formulas solver initial inherited resident started
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked, _merge, _fourth, _nodes⟩ := components
      have bounds := SourceCurrentParentUniformRanges.resident_ranges formulas solver inventory budget seed.1
        original running memos current (by simpa only [checked] using frame) seed.2
        (by simpa only [checked] using fits) (by simpa only [checked] using known)
        owner.inherited owner.input (Schedule.parent_reserved bits budget seed room)
      simp only [Ranges.edgeCall, started]
      unfold Ranges.edgeBody
      split
      · exact bounds
      · trivial

private theorem check_phase {g s r e p h m c n budget : Nat} {first : Phase (bits + 2)}
    (last : Phase (bits + 2)) (actual : Reached g s r e p h m c n budget first last)
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2) :
    phaseRanges g s r e p h m c n budget last := by
  cases phaseEquation : last with
  | node fuel request before =>
      rw [phaseEquation] at actual
      rcases started : beginNode request before with ⟨handle, action, running⟩
      cases action with
      | ready result => simp only [phaseRanges, Ranges.nodeCall, started]
      | busy => simp only [phaseRanges, Ranges.nodeCall, started]
      | absent => simp only [phaseRanges, Ranges.nodeCall, started]
      | evaluate original =>
          simp only [phaseRanges, Ranges.nodeCall, started]
          exact check_phase (.body fuel original running)
            (.snoc actual (.node_evaluate started)) seed initial frame fits known inputs room
  | body fuel request before =>
      rw [phaseEquation] at actual
      cases shaped : request.value with
      | empty => simp only [phaseRanges, Ranges.nodeBody, shaped]
      | union => simp only [phaseRanges, Ranges.nodeBody, shaped]
      | reference => simp only [phaseRanges, Ranges.nodeBody, shaped]
      | mu => simp only [phaseRanges, Ranges.nodeBody, shaped]
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [phaseRanges, Ranges.nodeBody, shaped]
          | succ fuel =>
              simp only [phaseRanges, Ranges.nodeBody, shaped]
              exact check_phase (.rows fuel request.inherited original before)
                (.snoc actual (.body_rows shaped)) seed initial frame fits known inputs room
  | rows fuel inherited values before =>
      rw [phaseEquation] at actual
      cases values with
      | nil => simp only [phaseRanges, Ranges.rows]
      | cons original rest =>
          cases fuel with
          | zero => simp only [phaseRanges, Ranges.rows]
          | succ fuel =>
              simp only [phaseRanges, Ranges.rows]
              constructor
              · obtain ⟨next, final, current, _trace, post, returned, numeric, carrier, operands,
                    _below, _subset, currentRoom, _rest⟩ := SourceCurrentOuterInitialPrefix.reached
                    formulas solver seed actual initial frame fits known inputs room
                simp only [SourceCurrentOuterInitialPrefix.forecast, Schedule.rows] at currentRoom
                have parentRoom : Room bits (Schedule.parent budget current).2 := currentRoom.mono
                  ((Schedule.descendants_ge fuel budget (Schedule.parent budget current)).1.trans
                    (Schedule.rows_ge fuel budget
                      (Schedule.descendants fuel budget (Schedule.parent budget current))).1)
                exact edge_ranges formulas solver current post.context returned numeric carrier operands.1
                  (operands.2 original List.mem_cons_self) parentRoom
              · cases edgeDone : SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget
                    ⟨inherited, original⟩ before with
                | failed => trivial
                | done narrowed middle =>
                    change Ranges.descendants fuel g s r e p h m c n budget inherited narrowed middle ∧ _
                    constructor
                    · exact check_phase (.descendants fuel inherited narrowed middle)
                        (.snoc actual (.rows_edge edgeDone)) seed initial frame fits known inputs room
                    · cases descendantsDone : SourceCurrentAllocatedPartialWorker.descendants fuel g s r e p h m c n budget
                          inherited narrowed middle with
                      | failed => trivial
                      | done result after =>
                          exact check_phase (.rows fuel inherited rest after)
                            (.snoc actual (.rows_tail edgeDone descendantsDone)) seed initial frame fits known inputs room
  | descendants fuel inherited edge before =>
      rw [phaseEquation] at actual
      simp only [phaseRanges, Ranges.descendants]
      cases combinedEquation : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited
          before.checked.operations).1 with
      | error => trivial
      | ok result =>
          cases result with
          | none => trivial
          | some combined =>
              exact check_phase
                (.children fuel combined edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited))
                (.snoc actual (.descendants_children combinedEquation)) seed initial frame fits known inputs room
  | children fuel combined values before =>
      rw [phaseEquation] at actual
      cases combined with
      | contradiction => simp only [phaseRanges, Ranges.children]
      | live identity records =>
          simp only [phaseRanges, Ranges.children]
          exact check_phase (.walk fuel (.live identity records) 0 values before)
            (.snoc actual (.children_walk (by intro impossible; cases impossible))) seed initial frame fits known inputs room
  | walk fuel combined index values before =>
      rw [phaseEquation] at actual
      cases values with
      | nil => simp only [phaseRanges, Ranges.walk]
      | cons value rest =>
          cases fuel with
          | zero => simp only [phaseRanges, Ranges.walk]
          | succ fuel =>
              simp only [phaseRanges, Ranges.walk]
              constructor
              · exact check_phase
                  (.node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
                    (SourceCurrentAllocatedPartialGraph.descend before combined index).2)
                  (.snoc actual .walk_head) seed initial frame fits known inputs room
              · cases nodeDone : SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget
                    ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
                    (SourceCurrentAllocatedPartialGraph.descend before combined index).2 with
                | failed => trivial
                | done result middle =>
                    exact check_phase (.walk fuel combined (index + 1) rest middle)
                      (.snoc actual (.walk_tail nodeDone)) seed initial frame fits known inputs room
termination_by phaseRank last
decreasing_by
  all_goals
    simp_all only [phaseRank]
    omega

/-- The computed initial forecast supplies every literal reached worker range check. -/
theorem nodeCall_ranges {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before : Caller (bits + 2)} {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget (.node fuel request before) seed).2) :
    Ranges.nodeCall fuel g s r e p h m c n budget request before :=
  check_phase formulas solver (.node fuel request before) (.refl _) seed initial frame fits known
    ⟨inherited, available⟩ room

end MicroCFTA.SourceCurrentOuterInitialWorkerRanges

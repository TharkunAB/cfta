import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerRanges
import MicroCFTA.SourceCurrentSharedOuterInitialRanges
import MicroCFTA.SourceCurrentSharedOuterInitialActual

/-!
# Initial ranges through every actual shared outer prefix

Each reached Parent requires its range plan before its outcome is known.
A failed prefix skips only its unexecuted continuation. Actual successful
siblings supply the next Context and scheduled resource seed. One initial
phase Room supplies all such current reservations.

No whole-call success, future Context, field classification, or completed
suffix is an input. These predicates describe literal bounded execution.
They do not assert completion, larger-bound trace identity, graph-wide
Checks, or native and Haskell driver correspondence.
-/
namespace MicroCFTA.SourceCurrentSharedOuterInitialLiteralRanges
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
local notation "descend" => SourceCurrentAllocatedSharedPartialGraph.descend
local notation "prefixState" => SourceCurrentAllocatedSharedPartialGraph.prefixState
namespace Schedule
export SourceCurrentSharedOuterInitialSchedule
  (parent rebuild node body rows descendants children walk parent_ge rebuild_ge node_ge body_ge
    rows_ge descendants_ge children_ge walk_ge parent_reserved)
end Schedule
namespace Ranges
export SourceCurrentAllocatedSharedPartialWorkerRanges
  (After nodeCall nodeBody edgeCall edgeBody rows descendants children walk)
end Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.node fuel budget seed).2 →
    Ranges.nodeCall fuel g s r e p h m c n budget request before

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.body fuel budget seed).2 →
    Ranges.nodeBody fuel g s r e p h m c n budget request before

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values : List Edge} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Room bits (Schedule.rows fuel budget seed).2 →
    Ranges.rows fuel g s r e p h m c n budget inherited values before

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value : Edge} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    Room bits (Schedule.descendants fuel budget seed).2 →
    Ranges.descendants fuel g s r e p h m c n budget inherited value before

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values : List Node} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.children fuel budget seed).2 →
    Ranges.children fuel g s r e p h m c n budget combined values before

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values : List Node} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.walk fuel budget seed).2 →
    Ranges.walk fuel g s r e p h m c n budget combined index values before

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt formulas solver (bits := bits) smaller) :
    WalkAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined index values before inventory memos seed
    initial frame fits known inherited available room
  cases values with
  | nil => simp only [Ranges.walk]
  | cons value rest =>
      cases fuel with
      | zero => simp only [Ranges.walk]
      | succ fuel =>
          rw [Schedule.walk] at room
          simp only [Ranges.walk]
          obtain ⟨descentReceipt, descentFrame, descentFits, descentPost⟩ :=
            SourceCurrentInheritedNumeric.descent formulas solver inventory before memos combined index
              initial frame seed.2 fits inherited
          have headAvailable := descentPost.effects.keeps.available _ (available value List.mem_cons_self)
          have nodeRoom : Room bits (Schedule.node fuel budget seed).2 :=
            room.mono (Schedule.walk_ge fuel budget (Schedule.node fuel budget seed)).1
          refine ⟨nodes fuel (Nat.lt_succ_self _) seed descentPost.context descentFrame descentFits
            known descentReceipt.inherited headAvailable nodeRoom, ?_⟩
          cases first : SourceCurrentAllocatedSharedPartialWorker.nodeCall fuel g s r e p h m c n budget
              ⟨(descend before combined index).1, value⟩ (descend before combined index).2 with
          | failed fault after => simp only [Ranges.After]
          | done result middle =>
              change Ranges.walk fuel g s r e p h m c n budget combined (index + 1) rest middle
              obtain ⟨next, final, _graph, _reads, post, returnedFrame, returnedFits,
                  returnedKnown, _returned, _law⟩ :=
                SourceCurrentSharedOuterInitialActual.node_call formulas solver fuel
                  (request := ⟨(descend before combined index).1, value⟩) seed
                  descentPost.context descentFrame descentFits known descentReceipt.inherited headAvailable nodeRoom first
              have total := descentPost.trans post
              have tailAvailable : Values middle.checked.native.machine.heap rest :=
                fun child member => total.effects.keeps.available _ (available child (List.mem_cons_of_mem _ member))
              exact tails fuel (Nat.lt_succ_self _) (Schedule.node fuel budget seed)
                post.context returnedFrame returnedFits returnedKnown
                (inherited.grows total.effects.grows.constraint_growth) tailAvailable room

private theorem children_step (fuel : Nat) (walks : WalkAt formulas solver (bits := bits) fuel) :
    ChildrenAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined values before inventory memos seed
    initial frame fits known inherited available room
  cases combined with
  | contradiction => simp only [Ranges.children]
  | live identity records =>
      simp only [Ranges.children]
      exact walks seed initial frame fits known inherited available (by simpa only [Schedule.children] using room)

private theorem descendants_step (fuel : Nat) (child : ChildrenAt formulas solver (bits := bits) fuel) :
    DescendantsAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited value before inventory memos seed
    initial frame fits known inheritedReady resident room
  rw [Schedule.descendants] at room
  cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [Ranges.descendants, observed]
      | ok answer =>
          cases answer with
          | none => simp only [Ranges.descendants, observed]
          | some combined =>
              simp only [Ranges.descendants, observed]
              obtain ⟨chosen, receipt, prefixFrame, prefixFits, post⟩ :=
                SourceCurrentInheritedNumeric.resident_complete formulas solver inventory value inherited before memos
                  initial frame seed.2 fits (fun _ => resident) (fun _ => inheritedReady)
              have combinedEquation : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited
                  before.checked.operations).1 = .ok (some combined) := by rw [observed]
              have same := Option.some.inj (Except.ok.inj (receipt.actual.symm.trans combinedEquation))
              cases same
              have originalInputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ value resident
              have inputs : Values (prefixState before value inherited).checked.native.machine.heap value.children :=
                fun item member => post.effects.keeps.available _ (originalInputs item member)
              have childRoom : Room bits (Schedule.children fuel budget seed).2 :=
                room.mono (Schedule.rebuild_ge (Schedule.children fuel budget seed)).1
              exact child seed post.context prefixFrame prefixFits known receipt.combinedReady inputs childRoom

private theorem rows_step (fuel : Nat)
    (descendantsAt : ∀ smaller, smaller < fuel → DescendantsAt formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt formulas solver (bits := bits) smaller) :
    RowsAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited values before inventory memos seed
    initial frame fits known inheritedReady resident room
  cases values with
  | nil => simp only [Ranges.rows]
  | cons original rest =>
      cases fuel with
      | zero => simp only [Ranges.rows]
      | succ fuel =>
          have callRanges := SourceCurrentSharedOuterInitialRanges.rows_call_ranges formulas solver
            (g := g) (s := s) (r := r) (e := e) (p := p) (h := h) (m := m) (c := c) (n := n)
            (budget := budget) (fuel := fuel)
            (first := .rows (fuel + 1) inherited (original :: rest) before)
            seed (.refl _) initial frame fits known ⟨inheritedReady, resident⟩ room
          have headRanges : Ranges.edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before := by
            rcases started : beginEdge ⟨inherited, original⟩ before with ⟨handle, action, running⟩
            cases action with
            | ready result => simp only [Ranges.edgeCall, started]
            | busy => simp only [Ranges.edgeCall, started]
            | absent => simp only [Ranges.edgeCall, started]
            | evaluate owner =>
                simpa only [Ranges.edgeCall, started, Ranges.edgeBody] using callRanges handle owner running started
          rw [Schedule.rows] at room
          simp only [Ranges.rows]
          refine ⟨headRanges, ?_⟩
          cases first : SourceCurrentAllocatedSharedPartialWorker.edgeCall fuel g s r e p h m c n budget
              ⟨inherited, original⟩ before with
          | failed fault middle => simp only [Ranges.After]
          | done narrowed middle =>
              change Ranges.descendants fuel g s r e p h m c n budget inherited narrowed middle ∧
                Ranges.After (SourceCurrentAllocatedSharedPartialWorker.descendants fuel g s r e p h m c n budget
                  inherited narrowed middle) (fun _ after => Ranges.rows fuel g s r e p h m c n budget inherited rest after)
              let edgeSeed := Schedule.parent budget seed
              let childSeed := Schedule.descendants fuel budget edgeSeed
              have edgeRoom : Room bits edgeSeed.2 := room.mono
                ((Schedule.descendants_ge fuel budget edgeSeed).1.trans (Schedule.rows_ge fuel budget childSeed).1)
              obtain ⟨edgeInventory, edgeMemos, receipt, edgeFits, edgeKnown⟩ :=
                SourceCurrentSharedOuterEdgeGuardAlphabet.edge_call formulas solver inventory budget seed.1
                  ⟨inherited, original⟩ before memos initial frame seed.2 fits known inheritedReady
                  (resident original List.mem_cons_self) (Schedule.parent_reserved bits budget seed edgeRoom) first
              have childRoom : Room bits childSeed.2 := room.mono (Schedule.rows_ge fuel budget childSeed).1
              have afterInherited := inheritedReady.grows receipt.post.effects.grows.constraint_growth
              refine ⟨descendantsAt fuel (Nat.lt_succ_self _) edgeSeed receipt.post.context receipt.frame
                edgeFits edgeKnown afterInherited receipt.semantic.resident childRoom, ?_⟩
              cases second : SourceCurrentAllocatedSharedPartialWorker.descendants fuel g s r e p h m c n budget
                  inherited narrowed middle with
              | failed fault after => simp only [Ranges.After]
              | done result after =>
                  change Ranges.rows fuel g s r e p h m c n budget inherited rest after
                  obtain ⟨next, final, _graph, _reads, post, returnedFrame, returnedFits,
                      returnedKnown, _returned, _law⟩ :=
                    SourceCurrentSharedOuterInitialActual.descendants formulas solver fuel edgeSeed receipt.post.context
                      receipt.frame edgeFits edgeKnown afterInherited receipt.semantic.resident childRoom second
                  have total := receipt.post.trans post
                  have tailResident : Edges after.checked.native.machine.heap rest :=
                    fun row member => InternedEdgeResidency.edge_grows _ _ total.effects.keeps.growth _
                      (resident row (List.mem_cons_of_mem _ member))
                  exact tails fuel (Nat.lt_succ_self _) childSeed post.context returnedFrame returnedFits returnedKnown
                    (inheritedReady.grows total.effects.grows.constraint_growth) tailResident room

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt formulas solver (bits := bits) smaller) :
    NodeBodyAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before inventory memos seed
    initial frame fits known inherited available room
  cases request with
  | mk payload value =>
      cases value with
      | empty => simp only [Ranges.nodeBody]
      | union => simp only [Ranges.nodeBody]
      | reference => simp only [Ranges.nodeBody]
      | mu => simp only [Ranges.nodeBody]
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [Ranges.nodeBody]
          | succ fuel =>
              simp only [Ranges.nodeBody]
              rw [Schedule.body] at room
              have resident := InternedEdgeResidency.resident_edges _
                initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
              exact rowCalls fuel (Nat.lt_succ_self _) seed initial frame fits known inherited resident
                (room.mono (Schedule.rebuild_ge (Schedule.rows fuel budget seed)).1)

private theorem nodeCall_step (fuel : Nat) (body : NodeBodyAt formulas solver (bits := bits) fuel) :
    NodeCallAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before inventory memos seed
    initial frame fits known inherited available room
  rcases started : beginNode request before with ⟨handle, action, running⟩
  cases action with
  | ready result => simp only [Ranges.nodeCall, started]
  | busy => simp only [Ranges.nodeCall, started]
  | absent => simp only [Ranges.nodeCall, started]
  | evaluate owner =>
      simp only [Ranges.nodeCall, started]
      obtain ⟨current, ownerReady, _key, _cell⟩ :=
        SourceCurrentAllocatedSharedPartialCallSteps.node_start formulas solver initial inherited available started
      have components := beginNode_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked, _merge, _fourth, _nodes⟩ := components
      exact body seed current (by simpa only [checked] using frame) (by simpa only [checked] using fits)
        (by simpa only [checked] using known) ownerReady.inherited ownerReady.input
        (by simpa only [Schedule.node] using room)

private theorem all_ranges (fuel : Nat) :
    NodeCallAt formulas solver (bits := bits) fuel ∧ NodeBodyAt formulas solver (bits := bits) fuel ∧
    RowsAt formulas solver (bits := bits) fuel ∧ DescendantsAt formulas solver (bits := bits) fuel ∧
    ChildrenAt formulas solver (bits := bits) fuel ∧ WalkAt formulas solver (bits := bits) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walks : WalkAt formulas solver (bits := bits) fuel :=
        walk_step formulas solver fuel (fun smaller less => (ih smaller less).1)
          (fun smaller less => (ih smaller less).2.2.2.2.2)
      have child : ChildrenAt formulas solver (bits := bits) fuel := children_step formulas solver fuel walks
      have descendants : DescendantsAt formulas solver (bits := bits) fuel := descendants_step formulas solver fuel child
      have rows : RowsAt formulas solver (bits := bits) fuel :=
        rows_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.2.1)
          (fun smaller less => (ih smaller less).2.2.1)
      have body : NodeBodyAt formulas solver (bits := bits) fuel :=
        nodeBody_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.1)
      exact ⟨nodeCall_step formulas solver fuel body, body, rows, descendants, child, walks⟩

/-- Every literal node-demand prefix retains its reached shared Parent ranges. -/
theorem node_call (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.node fuel budget seed).2 →
    Ranges.nodeCall fuel g s r e p h m c n budget request before :=
  (all_ranges formulas solver (bits := bits) fuel).1

/-- Every literal node-body prefix retains its reached shared Parent ranges. -/
theorem node_body (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.body fuel budget seed).2 →
    Ranges.nodeBody fuel g s r e p h m c n budget request before :=
  (all_ranges formulas solver (bits := bits) fuel).2.1

/-- Every actual row prefix checks its Parent before inspecting the outcome. -/
theorem rows (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values : List Edge} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Room bits (Schedule.rows fuel budget seed).2 →
    Ranges.rows fuel g s r e p h m c n budget inherited values before :=
  (all_ranges formulas solver (bits := bits) fuel).2.2.1

/-- Actual inherited-prefix children retain their reached shared Parent ranges. -/
theorem descendants (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value : Edge} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    Room bits (Schedule.descendants fuel budget seed).2 →
    Ranges.descendants fuel g s r e p h m c n budget inherited value before :=
  (all_ranges formulas solver (bits := bits) fuel).2.2.2.1

/-- Both actual child branches retain all executed shared Parent ranges. -/
theorem children (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values : List Node} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.children fuel budget seed).2 →
    Ranges.children fuel g s r e p h m c n budget combined values before :=
  (all_ranges formulas solver (bits := bits) fuel).2.2.2.2.1

/-- Each actual indexed child prefix checks only executed continuations. -/
theorem walk (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values : List Node} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.walk fuel budget seed).2 →
    Ranges.walk fuel g s r e p h m c n budget combined index values before :=
  (all_ranges formulas solver (bits := bits) fuel).2.2.2.2.2

end MicroCFTA.SourceCurrentSharedOuterInitialLiteralRanges

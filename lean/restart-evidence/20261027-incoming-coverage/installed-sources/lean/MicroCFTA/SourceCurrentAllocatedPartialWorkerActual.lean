import MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges
import MicroCFTA.SourceCurrentAllocatedPartialWorkerLeafActual
import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition
import MicroCFTA.SourceCurrentAllocatedPartialActual
import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

/-!
# Actual receipts for the literal mutual outer worker

The proof follows the supplied successful bounded execution itself.
Every smaller prefix derives its own graph, strict reads, and reached checks.
Its existing semantic theorem supplies the next actual caller context.
Only reached machine ranges are assumed. No future graph, result law,
final invariant, or recursive completion callback is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialWorkerActual
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecksComposition
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialWorkerStability (bind_done_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget request before →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    ∃ final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual)

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    SourceCurrentAllocatedPartialWorkerRanges.nodeBody fuel g s r e p h m c n budget request before →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    ∃ final, ∃ actual : NodeBody budget request before result after,
      NodeBodyReads formulas solver actual memos final ∧ Checks (nodeBodyTrace actual)

private def EdgeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    SourceCurrentAllocatedPartialWorkerRanges.edgeCall fuel g s r e p h m c n budget request before →
    edgeCall fuel g s r e p h m c n budget request before = .done result after →
    ∃ final, ∃ actual : EdgeCall budget request before result after,
      EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual)

private def EdgeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    SourceCurrentAllocatedPartialWorkerRanges.edgeBody fuel g s r e p h m c n budget request before →
    edgeBody fuel g s r e p h m c n budget request before = .done result after →
    ∃ final, ∃ actual : EdgeBody budget request before result after,
      EdgeBodyReads formulas solver actual memos final ∧ Checks (edgeBodyTrace actual)

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values : List Edge} {before after : Caller width} {result : List Edge}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    SourceCurrentAllocatedPartialWorkerRanges.rows fuel g s r e p h m c n budget inherited values before →
    rows fuel g s r e p h m c n budget inherited values before = .done result after →
    ∃ final, ∃ actual : Rows budget inherited values before result after,
      RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual)

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value : Edge} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    SourceCurrentAllocatedPartialWorkerRanges.descendants fuel g s r e p h m c n budget inherited value before →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    ∃ final, ∃ actual : Descendants budget inherited value before result after,
      DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual)

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values : List Node} {before after : Caller width} {result : List Node}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    SourceCurrentAllocatedPartialWorkerRanges.children fuel g s r e p h m c n budget combined values before →
    children fuel g s r e p h m c n budget combined values before = .done result after →
    ∃ final, ∃ actual : Children budget combined values before result after,
      ChildrenReads formulas solver actual memos final ∧ Checks (childrenTrace actual)

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values : List Node} {before after : Caller width} {result : List Node}
    {inventory : Inventory} {memos : Memos},
    Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    SourceCurrentAllocatedPartialWorkerRanges.walk fuel g s r e p h m c n budget combined index values before →
    walk fuel g s r e p h m c n budget combined index values before = .done result after →
    ∃ final, ∃ actual : Walk budget combined index values before result after,
      WalkReads formulas solver actual memos final ∧ Checks (walkTrace actual)

private theorem edgeBody_step (fuel : Nat) : EdgeBodyAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos initial inherited resident ranges done
  have localRanges := SourceCurrentAllocatedPartialWorkerRanges.edgeBody_of_done ranges done
  obtain ⟨next, final, actual, reads, _receipt, _post⟩ :=
    SourceCurrentAllocatedPartialWorkerLeafActual.edgeBody_verified formulas solver initial inherited resident localRanges done
  exact ⟨final, actual, reads, edge_body actual (resident_ranges localRanges)⟩

private theorem edgeCall_step (fuel : Nat) : EdgeCallAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos initial inherited resident ranges done
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  cases action with
  | ready value =>
      simp only [edgeCall, started] at done
      cases done
      exact ⟨memos, .hit started, .hit (started := started), edge_hit started⟩
  | evaluate original =>
      have bodyRanges := SourceCurrentAllocatedPartialWorkerRanges.edgeCall_of_evaluate ranges started
      simp only [edgeCall, started] at done
      obtain ⟨value, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp done
      cases last
      obtain ⟨runningContext, owner, _, _⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      obtain ⟨final, actual, reads, checks⟩ := edgeBody_step formulas solver fuel
        runningContext owner.inherited owner.input bodyRanges first
      exact ⟨final, .evaluate started actual, .evaluate (started := started) reads,
        edge_evaluate started actual checks⟩
  | busy | absent => simp only [edgeCall, started] at done; cases done

private theorem nodeCall_step (fuel : Nat) (body : NodeBodyAt formulas solver (width := width) fuel) :
    NodeCallAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos initial inherited available ranges done
  rcases started : beginNode request before with ⟨handle, action, running⟩
  cases action with
  | ready value =>
      simp only [nodeCall, started] at done
      cases done
      exact ⟨memos, .hit started, .hit (started := started), node_hit started⟩
  | evaluate original =>
      have bodyRanges := SourceCurrentAllocatedPartialWorkerRanges.nodeCall_of_evaluate ranges started
      simp only [nodeCall, started] at done
      obtain ⟨value, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp done
      cases last
      obtain ⟨runningContext, owner, _, _⟩ :=
        SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
      obtain ⟨final, actual, reads, checks⟩ := body runningContext owner.inherited owner.input bodyRanges first
      exact ⟨final, .evaluate started actual, .evaluate (started := started) reads,
        node_evaluate started actual checks⟩
  | busy | absent => simp only [nodeCall, started] at done; cases done

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt formulas solver (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt formulas solver (width := width) smaller) :
    WalkAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget combined index values before after result inventory memos initial inherited available ranges done
  cases values with
  | nil =>
      simp only [walk] at done
      cases done
      exact ⟨memos, .nil, .nil, walk_nil⟩
  | cons value rest =>
      cases fuel with
      | zero => simp only [walk] at done; cases done
      | succ fuel =>
          simp only [walk] at done
          obtain ⟨headValue, middle, first, remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨restValues, finalState, tail, last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          simp only [SourceCurrentAllocatedPartialWorkerRanges.walk] at ranges
          have tailRanges := SourceCurrentAllocatedPartialWorkerRanges.after_of_done ranges.2 first
          obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver
            inventory before memos initial combined index inherited
          obtain ⟨headMemos, headGraph, headReads, headChecks⟩ := nodes fuel (Nat.lt_succ_self _)
            (request := ⟨(descend before combined index).1, value⟩) (before := (descend before combined index).2)
            descentPost.context descentReceipt.inherited
            (descentPost.effects.keeps.available _ (available value List.mem_cons_self)) ranges.1 first
          obtain ⟨headInventory, headPost, _headAvailable, _headLaw⟩ :=
            SourceCurrentAllocatedPartialActual.node_call formulas solver headReads inventory headChecks
              descentPost.context descentReceipt.inherited
              (descentPost.effects.keeps.available _ (available value List.mem_cons_self))
          have firstPost := descentPost.trans headPost
          have tailAvailable : Values middle.checked.native.machine.heap rest :=
            fun child member => firstPost.effects.keeps.available _ (available child (List.mem_cons_of_mem _ member))
          obtain ⟨final, tailGraph, tailReads, tailChecks⟩ := tails fuel (Nat.lt_succ_self _)
            headPost.context (inherited.grows firstPost.effects.grows.constraint_growth) tailAvailable tailRanges tail
          exact ⟨final, .cons headGraph tailGraph, .cons headReads tailReads,
            walk_cons headGraph tailGraph headChecks tailChecks⟩

private theorem children_step (fuel : Nat) (walks : WalkAt formulas solver (width := width) fuel) :
    ChildrenAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget combined values before after result inventory memos initial inherited available ranges done
  cases combined with
  | contradiction =>
      simp only [SourceCurrentAllocatedPartialWorker.children] at done
      cases done
      exact ⟨memos, .contradiction, .contradiction, children_contradiction⟩
  | live identity records =>
      simp only [SourceCurrentAllocatedPartialWorker.children] at done
      simp only [SourceCurrentAllocatedPartialWorkerRanges.children] at ranges
      obtain ⟨final, actual, reads, checks⟩ := walks initial inherited available ranges done
      exact ⟨final, .live actual, .live reads, children_live actual checks⟩

private theorem descendants_step (fuel : Nat) (child : ChildrenAt formulas solver (width := width) fuel) :
    DescendantsAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget inherited value before after result inventory memos initial inheritedReady resident ranges done
  cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [descendants, observed] at done; cases done
      | ok answer =>
          cases answer with
          | none => simp only [descendants, observed] at done; cases done
          | some combined =>
              have prefixSame : prefixState before value inherited =
                  advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                    ⟨before.checked.native.machine.heap, operations⟩) before.fourth before.merge := by
                simp only [prefixState, SourceCurrentAllocatedInheritedPrefix.state, observed]
              simp only [descendants, observed] at done
              rw [← prefixSame] at done
              obtain ⟨values, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              simp only [SourceCurrentAllocatedPartialWorkerRanges.descendants, observed] at ranges
              have combinedEquation : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited
                  before.checked.operations).1 = .ok (some combined) := by rw [observed]
              obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver
                inventory before memos initial value inherited combined resident inheritedReady combinedEquation
              have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges value.entry.key value resident
              have childInputs : Values (prefixState before value inherited).checked.native.machine.heap value.children :=
                fun item member => prefixPost.effects.keeps.available _ (inputs item member)
              obtain ⟨final, actual, reads, checks⟩ := child prefixPost.context prefixReceipt.combinedReady childInputs ranges first
              exact ⟨final, .run combinedEquation actual, .run (combined := combinedEquation) reads,
                descendants_run combinedEquation actual checks⟩

private theorem rows_step (fuel : Nat)
    (descend : ∀ smaller, smaller < fuel → DescendantsAt formulas solver (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt formulas solver (width := width) smaller) :
    RowsAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget inherited values before after result inventory memos initial inheritedReady resident ranges done
  cases values with
  | nil =>
      simp only [rows] at done
      cases done
      exact ⟨memos, .nil, .nil, rows_nil⟩
  | cons original rest =>
      cases fuel with
      | zero => simp only [rows] at done; cases done
      | succ fuel =>
          simp only [rows] at done
          obtain ⟨narrowed, middle, first, remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨edgeResult, current, second, remaining⟩ := (bind_done_iff _ _ _ _).mp remaining
          obtain ⟨restResults, finalState, tail, last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          simp only [SourceCurrentAllocatedPartialWorkerRanges.rows] at ranges
          have nextRanges := SourceCurrentAllocatedPartialWorkerRanges.after_of_done ranges.2 first
          have tailRanges := SourceCurrentAllocatedPartialWorkerRanges.after_of_done nextRanges.2 second
          obtain ⟨edgeMemos, edgeGraph, edgeReads, edgeChecks⟩ := edgeCall_step formulas solver fuel initial inheritedReady
            (resident original List.mem_cons_self) ranges.1 first
          obtain ⟨edgeInventory, edgePost, narrowedResident, _edgeLaw⟩ :=
            SourceCurrentAllocatedPartialActual.edge_call formulas solver edgeReads inventory edgeChecks initial inheritedReady
              (resident original List.mem_cons_self)
          obtain ⟨childMemos, childGraph, childReads, childChecks⟩ := descend fuel (Nat.lt_succ_self _)
            edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident nextRanges.1 second
          obtain ⟨childInventory, childPost, _resultResident, _childLaw⟩ :=
            SourceCurrentAllocatedPartialActual.descendants formulas solver childReads edgeInventory childChecks edgePost.context
              (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident
          have firstPost := edgePost.trans childPost
          have tailResident : Edges current.checked.native.machine.heap rest :=
            fun edge member => InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _
              (resident edge (List.mem_cons_of_mem _ member))
          obtain ⟨final, tailGraph, tailReads, tailChecks⟩ := tails fuel (Nat.lt_succ_self _)
            childPost.context (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident tailRanges tail
          exact ⟨final, .cons edgeGraph childGraph tailGraph, .cons edgeReads childReads tailReads,
            rows_cons edgeGraph childGraph tailGraph edgeChecks childChecks tailChecks⟩

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt formulas solver (width := width) smaller) :
    NodeBodyAt formulas solver (width := width) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos initial inherited available ranges done
  cases request with
  | mk inheritedValue value =>
      cases value with
      | empty =>
          simp only [nodeBody] at done
          cases done
          exact ⟨memos, .empty, .empty, empty⟩
      | union entry members depth free =>
          simp only [nodeBody] at done
          cases done
          exact ⟨memos, .union, .union, union⟩
      | reference name => simp only [nodeBody] at done; cases done
      | mu entry body depth ordinary =>
          cases observed : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
          | pending => simp only [nodeBody, observed] at done; cases done
          | done value heap =>
              simp only [nodeBody, observed] at done
              cases done
              exact ⟨memos, .binder observed, .binder (actual := observed), binder observed⟩
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at done; cases done
          | succ fuel =>
              simp only [nodeBody] at done
              obtain ⟨results, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              simp only [SourceCurrentAllocatedPartialWorkerRanges.nodeBody] at ranges
              have edges := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _
                available.resident
              obtain ⟨final, actual, reads, checks⟩ := rowCalls fuel (Nat.lt_succ_self _) initial inherited edges ranges first
              exact ⟨final, .ordinary actual, .ordinary reads, ordinary actual checks⟩

private theorem all_actual (fuel : Nat) :
    NodeCallAt formulas solver (width := width) fuel ∧ NodeBodyAt formulas solver (width := width) fuel ∧
    RowsAt formulas solver (width := width) fuel ∧ DescendantsAt formulas solver (width := width) fuel ∧
    ChildrenAt formulas solver (width := width) fuel ∧ WalkAt formulas solver (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walks : WalkAt formulas solver (width := width) fuel :=
        walk_step formulas solver fuel (fun smaller less => (ih smaller less).1)
        (fun smaller less => (ih smaller less).2.2.2.2.2)
      have children : ChildrenAt formulas solver (width := width) fuel := children_step formulas solver fuel walks
      have descendants : DescendantsAt formulas solver (width := width) fuel := descendants_step formulas solver fuel children
      have rows : RowsAt formulas solver (width := width) fuel :=
        rows_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.2.1)
        (fun smaller less => (ih smaller less).2.2.1)
      have body : NodeBodyAt formulas solver (width := width) fuel :=
        nodeBody_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.1)
      exact ⟨nodeCall_step formulas solver fuel body, body, rows, descendants, children, walks⟩

/-- A supplied successful node call derives its own strict graph and complete semantic receipt. -/
theorem nodeCall_verified
    {fuel g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget request before)
    (done : nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  obtain ⟨final, actual, reads, checks⟩ := (all_actual formulas solver fuel).1 initial inheritedReady available ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver
    reads inventory checks initial inheritedReady available
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- A supplied successful node body derives its own strict graph and complete semantic receipt. -/
theorem nodeBody_verified
    {fuel g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeBody fuel g s r e p h m c n budget request before)
    (done : nodeBody fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ actual : NodeBody budget request before result after,
      NodeBodyReads formulas solver actual memos final ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  obtain ⟨final, actual, reads, checks⟩ := (all_actual formulas solver fuel).2.1 initial inheritedReady available ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_body formulas solver
    reads inventory checks initial inheritedReady available
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- A supplied successful edge call derives its own strict graph and complete semantic receipt. -/
theorem edgeCall_verified
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall fuel g s r e p h m c n budget request before)
    (done : edgeCall fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ actual : EdgeCall budget request before result after,
      EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨final, actual, reads, checks⟩ := edgeCall_step formulas solver fuel initial inheritedReady resident ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.edge_call formulas solver
    reads inventory checks initial inheritedReady resident
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- A supplied successful parent body derives its own strict graph and complete semantic receipt. -/
theorem edgeBody_verified
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.edgeBody fuel g s r e p h m c n budget request before)
    (done : edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ actual : EdgeBody budget request before result after,
      EdgeBodyReads formulas solver actual memos final ∧ Checks (edgeBodyTrace actual) ∧
      Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨final, actual, reads, checks⟩ := edgeBody_step formulas solver fuel initial inheritedReady resident ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.edge_body formulas solver
    reads inventory checks initial inheritedReady resident
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- Successful row traversal derives its own strict graph and complete semantic receipt. -/
theorem rows_verified
    {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {values : List Edge} {before after : Caller width} {result : List Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.rows fuel g s r e p h m c n budget inherited values before)
    (done : rows fuel g s r e p h m c n budget inherited values before = .done result after) :
    ∃ next final, ∃ actual : Rows budget inherited values before result after,
      RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual) ∧
      Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap result ∧ SourceCurrentAllocatedPartialForestLanguage.RowsLaw formulas solver actual := by
  obtain ⟨final, actual, reads, checks⟩ := (all_actual formulas solver fuel).2.2.1 initial inheritedReady resident ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver
    reads inventory checks initial inheritedReady resident
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- Successful descendant traversal derives its own strict graph and complete semantic receipt. -/
theorem descendants_verified
    {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {value : Edge} {before after : Caller width} {result : Edge}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Resident before.checked.native.machine.heap value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.descendants fuel g s r e p h m c n budget inherited value before)
    (done : descendants fuel g s r e p h m c n budget inherited value before = .done result after) :
    ∃ next final, ∃ actual : Descendants budget inherited value before result after,
      DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
      Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver ⟨inherited, value⟩ result := by
  obtain ⟨final, actual, reads, checks⟩ := (all_actual formulas solver fuel).2.2.2.1 initial inheritedReady resident ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.descendants formulas solver
    reads inventory checks initial inheritedReady resident
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- A supplied successful child traversal derives its own strict graph and complete semantic receipt. -/
theorem children_verified
    {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {values : List Node} {before after : Caller width} {result : List Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.children fuel g s r e p h m c n budget combined values before)
    (done : children fuel g s r e p h m c n budget combined values before = .done result after) :
    ∃ next final, ∃ actual : Children budget combined values before result after,
      ChildrenReads formulas solver actual memos final ∧ Checks (childrenTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap result ∧ SourceCurrentAllocatedPartialWalkLanguage.ChildrenLaw formulas solver actual := by
  obtain ⟨final, actual, reads, checks⟩ := (all_actual formulas solver fuel).2.2.2.2.1 initial inheritedReady available ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.children formulas solver
    reads inventory checks initial inheritedReady available
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- A supplied successful indexed walk derives its own strict graph and complete semantic receipt. -/
theorem walk_verified
    {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values : List Node} {before after : Caller width} {result : List Node}
    {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.walk fuel g s r e p h m c n budget combined index values before)
    (done : walk fuel g s r e p h m c n budget combined index values before = .done result after) :
    ∃ next final, ∃ actual : Walk budget combined index values before result after,
      WalkReads formulas solver actual memos final ∧ Checks (walkTrace actual) ∧
      Post formulas solver next before after final ∧ Values after.checked.native.machine.heap result ∧ SourceCurrentAllocatedPartialWalkLanguage.WalkLaw formulas solver actual := by
  obtain ⟨final, actual, reads, checks⟩ := (all_actual formulas solver fuel).2.2.2.2.2 initial inheritedReady available ranges done
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.walk formulas solver
    reads inventory checks initial inheritedReady available
  exact ⟨next, final, actual, reads, checks, post, output, law⟩

/-- A literal successful root reduction preserves the full language at its actual returned caller. -/
theorem root_exact
    {fuel g s r e p h m c n budget identity : Nat} {value result : Node}
    {before after : Caller width} {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget
      ⟨.live identity [], value⟩ before)
    (done : nodeCall fuel g s r e p h m c n budget ⟨.live identity [], value⟩ before = .done result after) :
    ∃ next final, ∃ actual : NodeCall budget ⟨.live identity [], value⟩ before result after,
      NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨final, actual, reads, checks⟩ := (all_actual formulas solver fuel).1
    initial inheritedReady available ranges done
  obtain ⟨next, post, resident, law⟩ := SourceCurrentAllocatedPartialActual.root_exact formulas solver
    reads checks initial inheritedReady available
  exact ⟨next, final, actual, reads, checks, post, resident, law⟩

end MicroCFTA.SourceCurrentAllocatedPartialWorkerActual

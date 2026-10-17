import MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainEdge
import MicroCFTA.SourceCurrentAllocatedPartialPlainTerminal
import MicroCFTA.SourceCurrentAllocatedPartialStepEffects

/-!
# Initial support for plain recursion in mixed outer tables

The rank hypothesis is an internal induction interface. Actual allocation
prefixes retain the conditional store and filtered active bound. A node
publication adds only its exact captured owner below the previous bound.
Terminal bodies construct their own reads and same-caller return.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainSupport
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove)
open SourceCurrentAllocatedPartialActiveOrder (nodeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedPartialPlainTerminal (Terminal)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable {width : Nat}

section Recursion
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
/-- A constructed node call retains its own reads, checks, state, and language law. -/
def NodeResult (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat)
    (request : NodeRequest) (before : Caller width) (memos : Memos) : Prop :=
  ∃ result after next final, ∃ actual : NodeCall budget request before result after,
    NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
    Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
    Stored after ∧ NodeLaw formulas solver request result

/-- Smaller-rank calls may use arbitrary initial callers that satisfy the same invariants. -/
def Below (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget rank : Nat) : Prop :=
  ∀ {inventory : Inventory} {before : Caller width} {memos : Memos} (request : NodeRequest),
    nodeRank request < rank → Context formulas solver inventory before memos →
    SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited →
    Available before.checked.native.machine.heap request.value → SourceEqualityPartialPlainRegion.Region request.value →
    Stored before → ActiveAbove (nodeRank request) before →
    NodeResult formulas solver budget request before memos

end Recursion

/-- Actual node publication admits every smaller filtered bound. -/
theorem node_push
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {request owner : NodeRequest} {before running : Caller width} {handle lower : Nat}
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (active : ActiveAbove (nodeRank request) before) (smaller : lower < nodeRank request)
    (started : beginNode request before = (handle, .evaluate owner, running)) : ActiveAbove lower running := by
  have cell := (SourceCurrentAllocatedPartialFrames.beginNode_owner request before handle owner running
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid sound.valid) started).1
  have same := SourceCurrentAllocatedPartialActiveOrder.node_owner_rank formulas solver sound coherent inherited available started
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  constructor
  · intro other original found region
    by_cases equal : other = handle
    · subst other
      have owners := congrArg FlatMemoThunk.Cell.request (Option.some.inj (cell.symm.trans found))
      change owner = original at owners
      rw [← owners, same]
      exact smaller
    · have observed : (FlatMemoThunk.demand published.1 published.2).2.cells other = some ⟨original, .evaluating⟩ := by
        change (beginNode request before).2.2.nodeResults.cells other = _
        simpa only [started] using found
      have handles : published.1 = handle := congrArg Prod.fst started
      have different : other ≠ published.1 := fun same => equal (same.trans handles)
      have old := FlatMemoThunk.lookup_running_before request.key request before.nodeResults other original
        (FlatMemoThunk.demand_running_before_other published.1 other published.2 original different observed)
      exact Nat.lt_trans smaller (active.nodes other original old region)
  · intro other original found plain
    have parts := beginNode_components request before
    rw [started] at parts
    dsimp only at parts
    exact Nat.lt_trans smaller (active.edges other original (by simpa only [parts.2.2.2] using found) plain)

section Prefixes
variable [DecidableEq (EdgeKey Symbol Guard)] {bound : Nat}
/-- Indexed descent constructs its literal payload and retains all current caller facts. -/
theorem descent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (combined : EqValue) (index : Nat)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (stored : Stored before) (active : ActiveAbove bound before) :
    SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory before combined index ∧
      Post formulas solver inventory before (descend before combined index).2 memos ∧
      Stored (descend before combined index).2 ∧ ActiveAbove bound (descend before combined index).2 := by
  obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos
    initial combined index inheritedReady
  exact ⟨receipt, post, stored,
    active.advance (descend before combined index).2.checked before.fourth before.merge⟩

/-- The resident inherited-first prefix constructs its own completed result and exact caller return. -/
theorem inherited_prefix
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (edge : EdgeValue Symbol Guard) (inherited : EqValue)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (stored : Stored before) (active : ActiveAbove bound before) :
    ∃ combined, SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory
        edge.entry.key.constraint inherited before.checked combined ∧
      Post formulas solver inventory before (prefixState before edge inherited) memos ∧
      Stored (prefixState before edge inherited) ∧ ActiveAbove bound (prefixState before edge inherited) := by
  obtain ⟨combined, receipt⟩ := SourceCurrentAllocatedInheritedPrefix.resident_finite formulas solver inventory
    edge inherited before.checked initial.ready initial.admitted resident inheritedReady
  have effects := SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos
    initial edge inherited combined resident inheritedReady receipt.actual
  exact ⟨combined, receipt, effects.2, stored,
    active.advance (SourceCurrentAllocatedInheritedPrefix.state before.checked edge.entry.key.constraint inherited)
      before.fourth before.merge⟩

end Prefixes

section Terminal
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {budget : Nat}

private theorem terminal_checks {request : NodeRequest} {before after : Caller width} {result : Node}
    (terminal : Terminal request.value) (actual : NodeBody budget request before result after) :
    Checks (nodeBodyTrace actual) := by
  cases actual <;> cases terminal
  all_goals
    intro edgeRequest edgeBefore edgeResult edgeAfter edgeActual reached
    cases reached with
    | step first rest => cases first

private theorem terminal_done {request : NodeRequest} {before after : Caller width} {result : Node}
    (terminal : Terminal request.value) (actual : NodeBody budget request before result after)
    (f g s r e p h m c n : Nat) :
    SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result after := by
  cases actual <;> cases terminal
  all_goals simp_all only [SourceCurrentAllocatedPartialWorker.nodeBody]

private theorem terminal_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : NodeRequest} {before : Caller width} {memos : Memos} {result : Node}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (stored : Stored before)
    (terminal : Terminal request.value) (actual : NodeBody budget request before result before)
    (reads : NodeBodyReads formulas solver actual memos memos) :
    NodeBodyReads formulas solver actual memos memos ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver inventory before before memos ∧ Available before.checked.native.machine.heap result ∧
      Stored before ∧ NodeLaw formulas solver request result ∧
      ∀ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result before := by
  have checks := terminal_checks terminal actual
  obtain ⟨next, post, resultAvailable, law⟩ :=
    SourceCurrentAllocatedPartialActual.node_body formulas solver reads inventory checks initial inheritedReady available
  exact ⟨reads, checks, Post.refl initial, resultAvailable, stored, law, terminal_done terminal actual⟩

/-- Initial caller facts construct the terminal graph, exact return, and literal zero-bound execution. -/
theorem terminal
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest) (initial : Context formulas solver inventory before memos)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (stored : Stored before)
    (terminal : Terminal request.value) :
    ∃ result, ∃ actual : NodeBody budget request before result before,
      NodeBodyReads formulas solver actual memos memos ∧ Checks (nodeBodyTrace actual) ∧
      Post formulas solver inventory before before memos ∧ Available before.checked.native.machine.heap result ∧
      Stored before ∧ NodeLaw formulas solver request result ∧
      ∀ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeBody f g s r e p h m c n budget request before = .done result before := by
  cases request with
  | mk inherited value =>
      cases terminal with
      | empty =>
          exact ⟨.empty, .empty, terminal_receipt formulas solver initial inheritedReady available stored .empty .empty .empty⟩
      | union =>
          exact ⟨_, .union, terminal_receipt formulas solver initial inheritedReady available stored .union .union .union⟩
      | @binder entry body depth ordinary =>
          have rebuilt := SourceCurrentAllocatedMuRebuild.resident_rebuild before.checked initial.ready initial.probes
            entry body depth ordinary available
          have unchanged : SourceCurrentAllocatedPartialState.advance before
              (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                ⟨before.checked.native.machine.heap, before.checked.operations⟩) before.fourth before.merge = before := by
            cases before
            rfl
          have actual : NodeBody budget ⟨inherited, .mu entry body depth ordinary⟩ before
              (cleanup (.mu entry body depth ordinary)) before := by
            simpa only [unchanged] using
              (NodeBody.binder (budget := budget) (inherited := inherited) rebuilt.1)
          have reads : NodeBodyReads formulas solver actual memos memos := by
            have rawReads : NodeBodyReads formulas solver
                (NodeBody.binder (budget := budget) (inherited := inherited) rebuilt.1) memos memos := .binder (actual := rebuilt.1)
            simpa only [unchanged] using rawReads
          exact ⟨_, actual, terminal_receipt formulas solver initial inheritedReady available stored .binder actual reads⟩

end Terminal

end MicroCFTA.SourceCurrentAllocatedPartialConditionalPlainSupport

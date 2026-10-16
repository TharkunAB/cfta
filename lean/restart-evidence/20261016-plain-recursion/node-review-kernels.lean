import MicroCFTA.SourceCurrentAllocatedPartialPlainNode

namespace MicroCFTA.PlainNodeIndependentReview
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
open SourceCurrentAllocatedPartialActiveOrder
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Region" => SourceEqualityPartialPlainRegion.Region
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

-- Initial facts construct a literal completed execution and its own graph and reads.
theorem construct_own_literal {width : Nat} {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (region : Region request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before) :
    ∃ result after next final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Stored after ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result ∧
      ∃ f g s r e p h m c n,
        SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before = .done result after := by
  obtain ⟨result, after, next, final, ⟨f, g, s, r, e, p, h, m, c, n, stable⟩,
    actual, reads, checks, post, output, retained, law⟩ :=
    SourceCurrentAllocatedPartialPlainNode.finite formulas solver budget request initial inherited available region stored active
  exact ⟨result, after, next, final, actual, reads, checks, post, retained, output, law,
    f, g, s, r, e, p, h, m, c, n,
    stable f g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩

-- The second node uses the first computed inventory and all of its warm caller state.
theorem two_current_nodes {width : Nat} {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (first second : NodeRequest) (initial : Context formulas solver inventory before memos)
    (firstReady : EqReady before.checked.operations.constraints first.inherited)
    (secondReady : EqReady before.checked.operations.constraints second.inherited)
    (firstAvailable : Available before.checked.native.machine.heap first.value)
    (secondAvailable : Available before.checked.native.machine.heap second.value)
    (firstRegion : Region first.value) (secondRegion : Region second.value) (stored : Stored before)
    (active : ActiveAbove (max (nodeRank first) (nodeRank second)) before) :
    ∃ result middle firstInventory middleMemos output after next final,
      (∃ actual : NodeCall budget first before result middle,
        NodeCallReads formulas solver actual memos middleMemos ∧ Checks (nodeCallTrace actual)) ∧
      (∃ actual : NodeCall budget second middle output after,
        NodeCallReads formulas solver actual middleMemos final ∧ Checks (nodeCallTrace actual)) ∧
      Post formulas solver firstInventory before middle middleMemos ∧
      Post formulas solver next middle after final ∧ Post formulas solver next before after final ∧
      Stored after ∧ ActiveAbove (max (nodeRank first) (nodeRank second)) after ∧
      NodeLaw formulas solver first result ∧ NodeLaw formulas solver second output := by
  obtain ⟨result, middle, firstInventory, middleMemos, _stable, actualFirst, firstReads, firstChecks,
    firstPost, _output, firstStored, firstLaw⟩ :=
    SourceCurrentAllocatedPartialPlainNode.finite formulas solver budget first initial firstReady firstAvailable
      firstRegion stored (active.mono (Nat.le_max_left _ _))
  have nextActive := (SourceCurrentAllocatedPartialActiveFrames.node_call actualFirst).activeExcept active
  obtain ⟨output, after, next, final, _stable, actualSecond, secondReads, secondChecks,
    lastPost, _output, lastStored, secondLaw⟩ :=
    SourceCurrentAllocatedPartialPlainNode.finite formulas solver budget second firstPost.context
      (secondReady.grows firstPost.effects.grows.constraint_growth)
      (firstPost.effects.keeps.available _ secondAvailable) secondRegion firstStored
      (nextActive.mono (Nat.le_max_right _ _))
  exact ⟨result, middle, firstInventory, middleMemos, output, after, next, final,
    ⟨actualFirst, firstReads, firstChecks⟩, ⟨actualSecond, secondReads, secondChecks⟩,
    firstPost, lastPost, firstPost.trans lastPost, lastStored,
    (SourceCurrentAllocatedPartialActiveFrames.node_call actualSecond).activeExcept nextActive, firstLaw, secondLaw⟩

-- Forward frames retain both exact ancestor cells; reverse frames restore the independent cap.
theorem protect_both_ancestors {width : Nat} {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : NodeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (region : Region request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before)
    (nodeHandle edgeHandle cap : Nat) (nodeOwner : NodeRequest) (edgeOwner : EdgeRequest)
    (nodeCell : before.nodeResults.cells nodeHandle = some ⟨nodeOwner, .evaluating⟩)
    (edgeCell : before.edgeResults.cells edgeHandle = some ⟨edgeOwner, .evaluating⟩)
    (ceiling : ActiveAbove cap before) :
    ∃ result after next final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Stored after ∧
      after.nodeResults.cells nodeHandle = some ⟨nodeOwner, .evaluating⟩ ∧
      after.edgeResults.cells edgeHandle = some ⟨edgeOwner, .evaluating⟩ ∧
      Cache.Extends before.nodeResults.table after.nodeResults.table ∧
      Cache.Extends before.edgeResults.table after.edgeResults.table ∧ ActiveAbove cap after := by
  obtain ⟨result, after, next, final, _stable, actual, reads, checks, post, _output, retained, _law⟩ :=
    SourceCurrentAllocatedPartialPlainNode.finite formulas solver budget request initial inherited available region stored active
  have frame := SourceCurrentAllocatedPartialFrames.node_call actual
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid initial.sound.valid)
  exact ⟨result, after, next, final, actual, reads, checks, post, retained,
    frame.node_running _ _ nodeCell, frame.edge_running _ _ edgeCell, frame.node_keys, frame.edge_keys,
    (SourceCurrentAllocatedPartialActiveFrames.node_call actual).activeExcept ceiling⟩

-- Empty inherited constraints give full language equality from a constructed call, without supplied success.
theorem empty_inherited_exact {width : Nat} {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget identity : Nat) (value : Node) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value) (region : Region value)
    (stored : Stored before) (active : ActiveAbove (nodeRank ⟨.live identity [], value⟩) before) :
    ∃ result after next final,
      Post formulas solver next before after final ∧ Stored after ∧
      Available after.checked.native.machine.heap result ∧
      SourceCurrentEmptinessMemo.Extends before.fourth after.fourth ∧ Cache.Extends before.merge after.merge ∧
      EndpointMemoGateTrace.Valid after.checked.native.machine.heap final ∧
      InternedFreshOrdinaryProbeHeap.Heap after.checked.native.machine.heap ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨result, after, next, final, _stable, actual, reads, checks, _post, _output, retained, _law⟩ :=
    SourceCurrentAllocatedPartialPlainNode.finite formulas solver budget ⟨.live identity [], value⟩
      initial inherited available region stored active
  obtain ⟨actualInventory, post, output, exactness⟩ := SourceCurrentAllocatedPartialActual.root_exact
    formulas solver reads checks initial inherited available
  exact ⟨result, after, actualInventory, final, post, retained, output, post.fourthRetained, post.retained,
    post.context.globals, post.context.probes, exactness⟩

end MicroCFTA.PlainNodeIndependentReview

#print axioms MicroCFTA.PlainNodeIndependentReview.construct_own_literal
#check @MicroCFTA.PlainNodeIndependentReview.construct_own_literal
#print axioms MicroCFTA.PlainNodeIndependentReview.two_current_nodes
#check @MicroCFTA.PlainNodeIndependentReview.two_current_nodes
#print axioms MicroCFTA.PlainNodeIndependentReview.protect_both_ancestors
#check @MicroCFTA.PlainNodeIndependentReview.protect_both_ancestors
#print axioms MicroCFTA.PlainNodeIndependentReview.empty_inherited_exact
#check @MicroCFTA.PlainNodeIndependentReview.empty_inherited_exact

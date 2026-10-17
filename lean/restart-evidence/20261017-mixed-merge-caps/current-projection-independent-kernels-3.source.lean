import MicroCFTA.SourceCurrentConstrainedCapMixedTarget

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.CurrentProjectionIndependentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

private def badPlan (symbol : Symbol) (guard : Guard) : InternedNestedConstruction.Syntax Symbol Guard :=
  .node [.mk symbol guard []]

private def badValue (symbol : Symbol) (guard : Guard) : Value Symbol Guard :=
  .node {identity := 0, key := .node [0]}
    [.mk {identity := 0, key := ⟨symbol, [], guard⟩} []] 0 []

set_option cbv.maxSteps 100000000 in
private theorem bad_computed (symbol : Symbol) (guard : Guard) :
    (match InternedFreshOrdinaryConstruction.build (badPlan symbol guard) [] InternedConstructorTemplates.empty with
    | .done value _ => value | .pending .. => .empty) = badValue symbol guard := by cbv

variable [DecidableEq Symbol]

/-- A source-built nonplain selected root constructs its own operand beside an open sibling. -/
theorem constructed_selected_open_operand
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (symbol : Symbol) (guard : Guard) (bad : ¬Plain guard)
    (before : Checked width) (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (current : Current before)
    (heap : before.native.machine.heap =
      (InternedFreshOrdinaryConstruction.build (badPlan symbol guard) [] InternedConstructorTemplates.empty).state)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    let values := [badValue symbol guard, Value.reference .depth]
    Cap Plain 1 (badValue symbol guard) ∧
      ¬SourceEqualityAnnotationLanguage.Annotated Plain (badValue symbol guard) ∧
      ¬MergedColdReaderClosedInputs.ClosedValues values ∧
      ∃ result after saved final,
        SourceCurrentAllocatedTargetGraph.Operand [0] values before SourceCurrentMemoMergeGraph.empty result after saved ∧
        SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0] values before
          SourceCurrentMemoMergeGraph.empty result after saved memos final ∧
        SourceCurrentConstrainedCapMemoMerge.Stored Plain saved ∧ Current after ∧ Cap Plain 1 result := by
  dsimp only
  obtain ⟨original, initial, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete (badPlan symbol guard)
  have same : original = badValue symbol guard := by simpa only [built] using bad_computed symbol guard
  subst original
  have sameHeap : before.native.machine.heap = initial := by simpa only [built, InternedNestedConstruction.Outcome.state] using heap
  have originalAvailable : Available before.native.machine.heap (badValue symbol guard) := by
    rw [sameHeap]
    exact (InternedFreshOrdinaryFacts.closed_verified (badPlan symbol guard)).result _ _ built
  have bounded : Cap Plain 1 (badValue symbol guard) := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, EdgeValue.children, List.nil_append] at member
    cases member
  have nonplain : ¬SourceEqualityAnnotationLanguage.Annotated Plain (badValue symbol guard) := by
    intro annotated
    cases annotated with
    | node _ _ _ _ guards _ => exact bad (guards _ List.mem_cons_self)
  have openSibling : ¬MergedColdReaderClosedInputs.ClosedValues
      [badValue symbol guard, Value.reference .depth] := by
    intro closed
    have impossible := closed (.reference .depth) (by simp)
    cases impossible
  have available : Values before.native.machine.heap [badValue symbol guard, Value.reference .depth] := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact originalAvailable
    · exact InternedNestedProvenance.depth_available _
  have domain : SourceEqualityProjectionPathDomain.ForestClosed [0]
      [badValue symbol guard, Value.reference .depth] := by
    simp [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
      SourceEqualityProjectionGraph.select, badValue, Value.free]
  have covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient (SourceCurrentMemoMergeGraph.empty : Memo) := by
    intro ambient key entry absent
    cases absent
  obtain ⟨result, after, saved, final, actual, receipt, merged, afterCurrent, cap⟩ :=
    SourceCurrentConstrainedCapMixedTarget.operand_complete 1 formulas solver inventory [0]
      [badValue symbol guard, Value.reference .depth] before SourceCurrentMemoMergeGraph.empty
      ready admitted available domain (SourceCurrentMemoMergeEffects.stored_empty _) covered memos valid
      (SourceCurrentConstrainedCapMemoMerge.stored_empty Plain) current (by
        intro value member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact bounded
        · exact .plain 1 (.reference .depth))
  exact ⟨bounded, nonplain, openSibling, result, after, saved, final, actual, receipt, merged, afterCurrent, cap⟩

/-- An ordinary child selector constructs its own projection while a different child stays open. -/
theorem selected_ordinary_open_sibling
    (symbol : Symbol) (guard : Guard)
    (parentEntry : Interned InternedBinderProtocol.NodeKey) (rowEntry : Interned (EdgeKey Symbol Guard))
    (before : State Symbol Guard) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain before)
    (available : Available before (.node parentEntry
      [.mk rowEntry [badValue symbol guard, .reference .depth]] 0 [.depth])) :
    let original := Value.node parentEntry [.mk rowEntry [badValue symbol guard, .reference .depth]] 0 [.depth]
    original.free ≠ [] ∧
      ∃ result after, SourceEqualityProjectionGraph.Project [0] original before result after ∧
        result.free = [] ∧ Cap Plain 1 result ∧ SourceCurrentConstrainedCapGuardHeap.Heap Plain after := by
  dsimp only
  have child : Cap Plain 1 (badValue symbol guard) := by
    apply Cap.node 0
    intro value member
    simp only [List.flatMap_cons, List.flatMap_nil, EdgeValue.children, List.nil_append] at member
    cases member
  have cap : Cap Plain 2 (.node parentEntry
      [.mk rowEntry [badValue symbol guard, .reference .depth]] 0 [.depth]) := by
    apply Cap.node 1
    intro value member
    simp only [List.flatMap_cons, List.flatMap_nil, EdgeValue.children, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact child
    · exact .plain 1 (.reference .depth)
  have domain : SourceEqualityProjectionPathDomain.NodeClosed [0] (.node parentEntry
      [.mk rowEntry [badValue symbol guard, .reference .depth]] 0 [.depth]) := by
    simp [SourceEqualityProjectionPathDomain.NodeClosed, SourceEqualityProjectionGraph.select, badValue, Value.free]
  obtain ⟨result, after, actual, _, _, _, closed⟩ := SourceEqualityProjectionPathComplete.node_complete [0]
    _ before semantic available domain
  have bounded := SourceCurrentConstrainedCapSelectedProjection.node Plain 2 actual semantic available domain
    (SourceCurrentConstrainedCapGuardNative.stored Plain before guards) cap
  exact ⟨by simp only [Value.free, List.cons_ne_self], result, after, actual, closed, bounded.2,
    SourceCurrentConstrainedCapProjectionGuard.node Plain actual semantic costs available guards⟩

/-- Two supplied actual queries rebase at both returns and reuse the first produced cap. -/
theorem serial_actual_queries
    (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {left right other first result : Value Symbol Guard} {before middle after : Checked width}
    {inventory : Inventory} {memos : Memos}
    (initial : Ready before) (current : Current before)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (otherAvailable : Available before.native.machine.heap other)
    (leftClosed : left.free = []) (rightClosed : right.free = []) (otherClosed : other.free = [])
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right) (otherCap : Cap Plain depth other)
    (firstActual : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before first middle memos)
    (secondActual : SourceCurrentAllocatedTargetQuery.Step first other middle result after) :
    Current middle ∧ Cap Plain depth first ∧ first.free = [] ∧
      Current after ∧ Cap Plain depth result ∧ result.free = [] ∧ SourceRecursiveIntersectionInputView.Original result ∧
      SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree result := by
  have firstResult := SourceCurrentConstrainedCapCurrentNative.step depth formulas solver firstActual.actual
    initial.good initial.semantic current leftAvailable rightAvailable leftClosed rightClosed leftCap rightCap
  have secondResult := SourceCurrentConstrainedCapCurrentNative.step depth formulas solver secondActual
    firstActual.ready.good firstActual.ready.semantic firstResult.1 firstActual.available
      (firstActual.effects.keeps.available other otherAvailable) firstResult.2.2.1 otherClosed firstResult.2.1 otherCap
  exact ⟨firstResult.1, firstResult.2.1, firstResult.2.2.1, secondResult⟩

#print axioms constructed_selected_open_operand
#check @constructed_selected_open_operand
#print axioms selected_ordinary_open_sibling
#check @selected_ordinary_open_sibling
#print axioms serial_actual_queries
#check @serial_actual_queries
end MicroCFTA.CurrentProjectionIndependentKernels

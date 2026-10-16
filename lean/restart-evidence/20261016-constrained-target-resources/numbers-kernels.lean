import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers

namespace TargetBudgetNumberChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open MergedOrdinaryHeight (height childrenHeight)

/-- Two additional operands square the tail profile and retain three operand charges. -/
theorem two_query_tail :
    foldRows 2 0 = 2 ∧ foldRows 2 1 = 4 ∧ foldRows 2 2 = 16 ∧
      foldNodes 3 2 1 1 0 = 3 ∧ foldNodes 3 2 1 1 1 = 15 ∧ foldNodes 3 2 1 1 2 = 51 ∧
      foldEdges 1 2 1 1 0 = 1 ∧ foldEdges 1 2 1 1 1 = 11 ∧ foldEdges 1 2 1 1 2 = 45 := by decide

/-- A zero initial arity still reserves the native sentinel arity after every added query. -/
theorem zero_arity_initial_limits :
    operandRows 1 1 0 1 = 1 ∧ targetRows 1 1 0 1 2 = 1 ∧
      nodeBudget 1 0 1 0 1 0 = 3 ∧ nodeBudget 1 0 1 0 1 2 = 15 ∧
      edgeBudget 1 0 1 0 1 0 = 1 ∧ edgeBudget 1 0 1 0 1 2 = 9 := by decide

/-- Caller limit widening and a longer tail retain all earlier row and request budgets. -/
theorem widened_caller_limits {firstRows lastRows firstArity lastArity firstCount lastCount
    firstDepth lastDepth firstBound lastBound firstSteps lastSteps : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) (count : firstCount ≤ lastCount)
    (depth : firstDepth ≤ lastDepth) (bound : firstBound ≤ lastBound) (steps : firstSteps ≤ lastSteps) :
    targetRows firstRows firstCount firstDepth firstBound firstSteps ≤ targetRows lastRows lastCount lastDepth lastBound lastSteps ∧
      nodeBudget firstRows firstArity firstCount firstDepth firstBound firstSteps ≤
        nodeBudget lastRows lastArity lastCount lastDepth lastBound lastSteps ∧
      edgeBudget firstRows firstArity firstCount firstDepth firstBound firstSteps ≤
        edgeBudget lastRows lastArity lastCount lastDepth lastBound lastSteps :=
  ⟨Nat.le_trans (targetRows_parameters_mono firstSteps rows count depth bound) (targetRows_mono _ _ _ _ steps),
    Nat.le_trans (node_parameters_mono firstSteps rows arity count depth bound) (node_mono _ _ _ _ _ steps),
    Nat.le_trans (edge_parameters_mono firstSteps rows arity count depth bound) (edge_mono _ _ _ _ _ steps)⟩

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The zero-query base constructs its actual seed operand and derives every budget fact from initial limits. -/
theorem seed_operand
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory) (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (profiles : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    ∃ output after saved final requests,
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo output after saved memos final ∧
      SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored saved ∧
      NodeShape (targetRows rows count depth bound 0) (max arity 1) output ∧ height output ≤ bound ∧
      SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.Trace before.native.machine.heap after.native.machine.heap requests ∧
      SourceCurrentAllocatedFiniteOrdinaryReservations.nodeRequests requests ≤ nodeBudget rows arity count depth bound 0 ∧
      SourceCurrentAllocatedFiniteOrdinaryReservations.edgeRequests requests ≤ edgeBudget rows arity count depth bound 0 ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget rows arity count depth bound 0 ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget rows arity count depth bound 0 := by
  obtain ⟨output, after, saved, final, requests, receipt, stored, resultProfile, resultHeight,
    trace, nodes, edges, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOperandResources.complete formulas solver inventory path values before memo
      ready admitted available physical profiles covered memos valid rows arity count depth bound profile lengthBound pathBound heightBound
  exact ⟨output, after, saved, final, requests, receipt, stored,
    NodeShape.mono output resultProfile (Nat.le_refl _) (Nat.le_max_left arity 1),
    resultHeight, trace, nodes, edges, nodeSupply, edgeSupply⟩

#print axioms two_query_tail
#check @two_query_tail
#print axioms zero_arity_initial_limits
#check @zero_arity_initial_limits
#print axioms widened_caller_limits
#check @widened_caller_limits
#print axioms seed_operand
#check @seed_operand
end TargetBudgetNumberChecks

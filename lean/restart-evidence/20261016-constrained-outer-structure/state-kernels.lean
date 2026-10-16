import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
namespace FiniteOrdinaryOuterStateKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedFiniteOrdinaryOuterState
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {width : Nat}

/-- Literal cold native and outer tables derive all three causal certificates. -/
theorem cold_tables (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (fourth : SourceCurrentEmptinessMemo.Memo) :
    Stored (SourceCurrentAllocatedPartialState.initial
      (⟨SourceRecursiveIntersectionThunks.initial width machine, operations⟩ : SourceEqualityNativeDemand.State width)
      SourceCurrentMemoMergeGraph.empty fourth) :=
  SourceCurrentAllocatedFiniteOrdinaryOuterState.initial _ _ _
    (SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored width machine)
    SourceCurrentAllocatedFiniteOrdinaryMergeCache.empty_stored

/-- An actual captured owner survives literal descent before structural Empty completion. -/
theorem node_start_descend_finish
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {candidate owner : NodeRequest} {before running : Caller width} {handle index : Nat}
    (stored : Stored before) (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints candidate.inherited)
    (available : Available before.checked.native.machine.heap candidate.value) (domain : DNode candidate.value)
    (started : beginNode candidate before = (handle, .evaluate owner, running)) :
    let middle := (SourceCurrentAllocatedPartialGraph.descend running owner.inherited index).2
    let after := finishNode handle .empty middle
    owner.value = candidate.value ∧ DNode owner.value ∧ owner.key = candidate.key ∧ Stored after ∧
      after.nodeResults.cells handle = some ⟨owner, .returned .empty⟩ ∧
      after.checked.native = running.checked.native ∧ after.merge = before.merge := by
  obtain ⟨same, ownerDomain, key⟩ := node_evaluate formulas solver candidate owner before running handle
    sound coherent inherited available domain started
  have current := SourceCurrentAllocatedPartialMemoSound.beginNode_evaluate_sound formulas solver candidate before
    sound inherited available handle owner running started
  have runningStored : Stored running := by simpa only [started] using stored.beginNode candidate
  have prefixStored := runningStored.descend owner.inherited index
  have cell : (SourceCurrentAllocatedPartialGraph.descend running owner.inherited index).2.nodeResults.cells handle =
      some ⟨owner, .evaluating⟩ := current.2.1
  have completed := prefixStored.finishNode .empty cell (fun _ => ⟨.empty, Nat.zero_le _⟩)
  have lower := beginNode_components candidate before
  rw [started] at lower
  exact ⟨same, ownerDomain, key, completed, finishNode_returned handle owner .empty _ cell, rfl, lower.2.1⟩

/-- A supplied warm edge observation gives strict child rank without a supplied owner or result law. -/
theorem warm_edge_children
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {candidate : EdgeRequest} {before after : Caller width} {handle : Nat} {result : EdgeValue Symbol Guard}
    (stored : Stored before) (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap candidate.value) (domain : DEdge candidate.value)
    (started : beginEdge candidate before = (handle, .ready result, after)) :
    after = before ∧ Stored after ∧ EdgeNarrow candidate.value result ∧
      ∀ inherited child, child ∈ result.children → DNode child ∧
        SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨inherited, child⟩ <
          SourceCurrentAllocatedPartialActiveOrder.edgeRank candidate := by
  obtain ⟨same, narrowed⟩ := stored.edge_ready formulas solver candidate after handle result sound coherent resident domain started
  refine ⟨same, same.symm ▸ stored, narrowed, ?_⟩
  intro inherited child member
  have smaller := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge candidate.inherited inherited result child member
  refine ⟨narrowed.1.member child member, ?_⟩
  simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank] at smaller ⊢
  have height := narrowed.2
  omega
end FiniteOrdinaryOuterStateKernels
#print axioms FiniteOrdinaryOuterStateKernels.cold_tables
#check @FiniteOrdinaryOuterStateKernels.cold_tables
#print axioms FiniteOrdinaryOuterStateKernels.node_start_descend_finish
#check @FiniteOrdinaryOuterStateKernels.node_start_descend_finish
#print axioms FiniteOrdinaryOuterStateKernels.warm_edge_children
#check @FiniteOrdinaryOuterStateKernels.warm_edge_children

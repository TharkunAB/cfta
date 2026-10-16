import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.UniformParentBudgetChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryGuardOwn (classBudget pathDepth)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "GP" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
section Physical
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- The current resident field derives the actual precheck. Its own bounds
-- transfer uniform initial headroom to the literal operation-state budget.
theorem resident_initial_headroom
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (bits : Nat) (before : SourceEqualityNativeDemand.State (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (edge : EdgeValue Symbol Guard) (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (inherited : SourceEqualityConstraintAllocation.Value)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (limits : Limits) (guards : GP limits edge) (rows arity bound : Nat) (shape : EdgeShape rows arity edge)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget limits rows arity bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget limits rows arity bound ≤ 2 ^ (bits + 2)) :
    ∃ loaded own branch,
      SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory edge.entry.key.constraint loaded inherited before own branch ∧
      before.native.machine.heap.nodes.next +
        SourceCurrentAllocatedFiniteOrdinaryParentResources.nodeBudget edge.entry.key.constraint loaded inherited before.operations
          rows arity edge.children.length (pathDepth limits) bound ≤ 2 ^ bits ∧
      before.native.machine.heap.edges.next +
        SourceCurrentAllocatedFiniteOrdinaryParentResources.edgeBudget edge.entry.key.constraint loaded inherited before.operations
          rows arity edge.children.length (pathDepth limits) bound ≤ 2 ^ (bits + 2) := by
  obtain ⟨loaded, own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.resident_complete formulas solver inventory
    before ready admitted edge resident inherited inheritedReady
  have budget := receipt_budget receipt limits (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard edge guards)
    rows arity edge.children.length bound (EdgeShape.arity edge shape)
  exact ⟨loaded, own, branch, receipt,
    Nat.le_trans (Nat.add_le_add_left budget.1 _) nodes, Nat.le_trans (Nat.add_le_add_left budget.2 _) edges⟩

-- Actual own records bound the entire right fold at the common final profile.
-- No class count, path count, or inherited-size conclusion is an input.
theorem actual_own_class_pass
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {original : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value} {before : SourceEqualityNativeDemand.State width}
    {records : List SourceEqualityClassOrder.Record}
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own (.classes records))
    (limits : Limits) (guards : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limits original)
    (rows arity count bound : Nat) (countBound : count ≤ arity) :
    SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget records rows arity count (pathDepth limits) bound ≤
      classBudget limits * classNodes (classBudget limits)
        (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.parentRows limits rows arity bound)
        (max arity 1) arity (pathDepth limits) bound ∧
    SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget records rows arity count (pathDepth limits) bound ≤
      classBudget limits * classEdges (classBudget limits)
        (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.parentRows limits rows arity bound)
        (max arity 1) arity (pathDepth limits) bound := by
  have classes := SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt receipt limits guards
  have budget := pass_budget records limits rows arity count bound classes.2.2.1 classes.2.1 countBound
  exact ⟨Nat.le_trans budget.1 (Nat.mul_le_mul_right _ classes.2.1),
    Nat.le_trans budget.2 (Nat.mul_le_mul_right _ classes.2.1)⟩

end Physical
-- A nullary parent pays for no child or class constructor and one parent edge.
theorem nullary_exact (limits : Limits) (rows bound : Nat) :
    nodeBudget limits rows 0 bound = 0 ∧ edgeBudget limits rows 0 bound = 1 := by
  simp only [nodeBudget, edgeBudget, classNodes, classEdges, Nat.zero_mul, Nat.mul_zero, Nat.zero_add, and_self]

#print axioms resident_initial_headroom
#check @resident_initial_headroom
#print axioms actual_own_class_pass
#check @actual_own_class_pass
#print axioms nullary_exact
#check @nullary_exact
end MicroCFTA.UniformParentBudgetChecks

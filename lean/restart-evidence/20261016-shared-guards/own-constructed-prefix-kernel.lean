import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.SharedGuardEvidence
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
open SourceCurrentAllocatedFiniteOrdinaryGuardOwn (classBudget pathDepth classSteps)
open SourceCurrentAllocatedFiniteOrdinaryGuardProfiles (edgeLimits)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)

/-- Initial resident finite syntax constructs the prefix before any result bounds are read. -/
theorem constructed_own_bounds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    {width : Nat} (before : SourceEqualityNativeDemand.State width)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (edge : EdgeValue Symbol Constraint) (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge edge)
    (inherited : SourceEqualityConstraintAllocation.Value)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (rows count height : Nat) :
    ∃ loaded own branch,
      SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory edge.entry.key.constraint loaded inherited before own branch ∧
      SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputRows loaded inherited before.operations
        rows count (pathDepth (edgeLimits edge)) height ≤ parentRows (edgeLimits edge) rows count height ∧
      ∀ records, branch = .classes records →
        classSteps records ≤ 2 * classBudget (edgeLimits edge) ∧
        (∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ pathDepth (edgeLimits edge)) := by
  have profile := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.edge_self edge domain
  have raw := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard edge profile
  obtain ⟨loaded, own, branch, actual⟩ := SourceCurrentAllocatedPrecheck.resident_complete
    formulas solver inventory before ready admitted edge resident inherited inheritedReady
  refine ⟨loaded, own, branch, actual,
    SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.local_rows actual _ raw rows count height, ?_⟩
  intro records same
  subst branch
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt_steps actual _ raw,
    (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt actual _ raw).2.2.2⟩

end MicroCFTA.SharedGuardEvidence

#print axioms MicroCFTA.SharedGuardEvidence.constructed_own_bounds
#check @MicroCFTA.SharedGuardEvidence.constructed_own_bounds

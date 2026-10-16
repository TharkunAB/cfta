import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeRoot

namespace MicroCFTA.QuantitativeRootIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialGraph (NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Plan" => SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The same finite root return instantiates its output bounds from computed original input limits. -/
theorem computed_input_profile (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {before : SourceCurrentAllocatedPartialState.State (bits + 2)} {memos : EndpointMemoGateTrace.Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node request.value)
    (stored : Stored before)
    (active : SourceCurrentAllocatedPartialActiveOrder.ActiveAbove
      (SourceCurrentAllocatedPartialActiveOrder.nodeRank request) before)
    (plan : Plan bits budget (.nodeCall request before)) :
    let input := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits request.value
    let guards := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.limits request.value
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ NodeNarrow request.value result ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧
        SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape
          (SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers.nodeRows input.1 input.2 guards
            (MergedOrdinaryHeight.height request.value)) (max input.2 1) result ∧
        SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
          (SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers.nodeGuards input.1 input.2 guards
            (MergedOrdinaryHeight.height request.value)) result := by
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, availableResult, kept, narrowed, quantitative, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeRoot.finite bits formulas solver budget request
      initial inherited available domain stored active plan
  have shapes := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.node_shape_self request.value domain
  have guards := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.node_self request.value domain
  have produced := quantitative _ _ _ _ shapes guards (Nat.le_refl _)
  exact ⟨result, after, next, final, stable, actual, reads, checks, post, availableResult, kept, narrowed, law, produced⟩

end MicroCFTA.QuantitativeRootIntegration

set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.QuantitativeRootIntegration.computed_input_profile
#check @MicroCFTA.QuantitativeRootIntegration.computed_input_profile

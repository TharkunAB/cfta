import MicroCFTA.SourceEmptinessDecisionCosts
import MicroCFTA.SourceSecondaryGateClassFields

/-!
# Cost retention between successive secondary class queries

Supported paths give the existing closed-result and semantic effects.
Actual projection and native execution retain costs in the same heaps.
A completed seeded query and decision therefore restore the older gate
invariant. The original forest need not be closed. Actual word checks,
completed exploration, and anchored path support remain explicit.
-/
namespace MicroCFTA.SourceSecondaryGateQueryCosts
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEmptinessClassFold SourceSecondaryGateScopedProjection
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- Actual supported folds retain costs at each projected operand and native request. -/
theorem fold_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  induction trace with
  | one operand => exact SourceEmptinessClassFoldCosts.operand_costs operand ready available costs
  | cons operand rest native ih =>
      have first := operand_effects unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp))
      have firstCosts := SourceEmptinessClassFoldCosts.operand_costs operand ready available costs
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have tailGrowth := grows_trans growth first.2.1.growth
      have tailSupport := fun path member => supported path (List.mem_cons_of_mem _ member)
      have remaining := SourceSecondaryGateClassFold.fold_effects unconstrained anchor anchorSemantic anchorReady
        rest first.1 tailInputs tailGrowth tailSupport
      have tailCosts := ih first.1 tailInputs tailGrowth tailSupport firstCosts
      exact native.cost_heap remaining.1 tailCosts (remaining.2.1.available _ first.2.2.1) remaining.2.2.1

/-- The actual seeded rotation retains costs without closing unrelated original children. -/
theorem seeded_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  cases paths with
  | nil => obtain ⟨_, rfl⟩ := trace; exact costs
  | cons seed rest =>
      exact fold_costs unconstrained anchor anchorSemantic anchorReady trace ready available growth
        (fun path member => supported path ((mem_seededPaths (seed :: rest) path).mp member)) costs

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Either actual decision answer retains every heap invariant needed by the next fresh gate. -/
theorem seeded_decision_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {query : Value Symbol Guard} {answer : Bool}
    {before middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (seeded : Seeded top conjoin values paths before query middle)
    (decision : SourceEmptinessDecision.Decision query middle answer after)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (costs : CostHeap before.machine.heap) (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ GateReady after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  have folded := SourceSecondaryGateClassFold.seeded_effects unconstrained anchor anchorSemantic anchorReady
    seeded ready available growth supported
  have foldedCosts := seeded_costs unconstrained anchor anchorSemantic anchorReady seeded ready available growth supported costs
  have foldedFields := SourceSecondaryGateClassFields.seeded_fields unconstrained anchor anchorSemantic anchorReady
    seeded ready available growth supported fields
  have decided := SourceEmptinessDecision.effects decision folded.1 foldedFields
  have finalCosts := SourceEmptinessDecisionCosts.decision_costs decision folded.1 foldedCosts
  exact ⟨decided.1, finalCosts, SourceEqualityExposureCosts.gate_ready decided.1.semantic finalCosts,
    folded.2.1.trans decided.2.1, decided.2.2⟩

end MicroCFTA.SourceSecondaryGateQueryCosts

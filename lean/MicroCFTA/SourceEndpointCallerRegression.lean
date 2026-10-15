import MicroCFTA.SourceEndpointGate
import MicroCFTA.SourceEqualityOuterCallerCycle

/-!
# The stronger endpoint guard on the preserved caller-cycle input

The original constructor computation supplies the first ordinary endpoint.
Its free-reference set is empty. The new descendant check has a concrete
constrained-Mu witness. Earlier cycle proofs retain their previous gate.
This result does not execute the whole current reduction or its memo tables.
-/
namespace MicroCFTA.SourceEndpointCallerRegression
open InternedConstructorTemplates InternedNestedConstruction
open SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

attribute [local cbv_eval] array_small

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- Read the first stored child from the actual original root construction. -/
noncomputable def observation : Option (Value Symbol Guard) :=
  match InternedFreshOrdinaryConstruction.build SourceEqualityOuterCallerCycle.expression [] empty with
  | .done (.node _ (edge :: _) _ _) _ => edge.children[0]?
  | _ => none

/-- Test exactly the source closed-endpoint case changed by the new guard. -/
noncomputable def changed (value : Value Symbol Guard) : Bool :=
  value.free.isEmpty && SourceEndpointReachability.reaches SourceMemoGate.unconstrained value

/-- Kernel evaluation finds the constrained descendant below the actual closed endpoint. -/
theorem actual_changed : observation.map changed = some true := by cbv

/-- Original construction supplies a closed endpoint with an explicit new-helper witness. -/
theorem closed_witness : ∃ value, observation = some value ∧ value.free = [] ∧
    SourceEndpointReachability.Witness SourceMemoGate.unconstrained value := by
  cases found : observation with
  | none => have impossible := actual_changed; simp [found] at impossible
  | some value =>
      have checked : changed value = true := by
        simpa only [found, Option.map_some, Option.some.injEq] using actual_changed
      simp only [changed, Bool.and_eq_true, List.isEmpty_iff] at checked
      exact ⟨value, rfl, checked.1, (SourceEndpointReachability.reaches_iff _ _).mp checked.2⟩

/-- Every certified readback of that endpoint now blocks the first equality path. -/
theorem certified_endpoint (value : Value Symbol Guard) (observed : observation = some value)
    (node : InternedFreshOrdinaryGateRank.Node Symbol Guard) (same : node.value = value)
    (edges : List (List (InternedFreshOrdinaryGateRank.Node Symbol Guard)))
    (view : InternedFreshOrdinaryGateRank.view node = .branches edges) (fuel : Nat) :
    ConstrainedRecursionGate.nodeMeets (InternedFreshOrdinaryGateRank.read SourceMemoGate.unconstrained)
        (fuel + 1) [] node = some false ∧
    EndpointRecursionGate.nodeMeets (SourceEndpointGate.read SourceMemoGate.unconstrained)
        (fuel + 1) [] node = some true := by
  obtain ⟨actual, found, closed, witness⟩ := closed_witness
  have equal : actual = value := Option.some.inj (found.symm.trans observed)
  cases equal
  exact SourceEndpointGate.closed_witness_changes SourceMemoGate.unconstrained node edges view
    (same ▸ closed) (same ▸ witness) fuel

end MicroCFTA.SourceEndpointCallerRegression

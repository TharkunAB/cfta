import MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
import MicroCFTA.SourceEqualityProjectionPathComplete

/-!
# Resources for repaired stored substitution and bounded row exposure

The initial causal store bounds full stored substitution and unfolding.
Reader bounds use their explicit proof fuel. They do not derive that fuel
from an initial selected path or supply a complete Operand forecast.
-/
namespace MicroCFTA.SourceCurrentAllocatedProjectionResources
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open InternedNestedConstruction (Outcome)
open InternedValueMassHeap (Stored)
open SourceCurrentAllocatedRecursiveMassTrace (ceiling charge massAfter credit)
open SourceCurrentAllocatedRecursiveMassMonotone
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem encoded_transform (value : Value Symbol Guard) (bound : Nat)
    (small : InternedValueMass.value value ≤ bound) :
    InternedFreshOrdinaryResultMass.transform (encode (leaves value) [] value) bound ≤ ceiling bound := by
  have encoded := InternedStoredEncodingMass.encode_bound (leaves value) [] value
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 3) small
  have count : InternedFreshOrdinaryAllocationBudget.nodeBudget (encode (leaves value) [] value) +
      InternedFreshOrdinaryAllocationBudget.edgeBudget (encode (leaves value) [] value) ≤
      SourceCurrentAllocatedRecursiveMassBudget.growthSteps bound := by
    unfold SourceCurrentAllocatedRecursiveMassBudget.growthSteps
    omega
  exact Nat.le_trans (InternedFreshOrdinaryUniformMass.transform_bound bound _ bound
    (InternedStoredEncodingWidth.encode_width _ [] value bound small))
    (Nat.le_trans (InternedFreshOrdinaryUniformMass.evolve_count_mono bound count bound)
      (Nat.le_max_right _ _))

/-- Every stored-substitution outcome fits the initial store schedule, including old winners. -/
theorem execute_bound (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (bound : Nat) (stored : Stored bound before)
    (available : Available before value) (replacements : Replacements before environment) :
    Stored (ceiling bound) (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state ∧
      (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state.nodes.next ≤ before.nodes.next + charge bound ∧
      (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state.edges.next ≤ before.edges.next + charge bound ∧
      ∀ result after, InternedFreshOrdinaryStoredSubstitution.execute value environment before = .done result after →
        InternedValueMass.value result ≤ ceiling bound := by
  have small := InternedValueMassHeap.available before stored value available
  have inputs := inputs_available value environment before available replacements
  have built := InternedFreshOrdinaryResultMass.build_bound (encode (leaves value) [] value)
    ((leaves value).map (input environment)) before bound stored
    (fun child member => InternedValueMassHeap.available before stored child (inputs child member))
  have larger := encoded_transform value bound small
  have counters := InternedStoredEncodingMass.execute_bound value environment before
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 3) small
  refine ⟨built.1.mono larger, ?_, ?_, fun result after done => Nat.le_trans (built.2 result after done) larger⟩
  all_goals unfold charge SourceCurrentAllocatedRecursiveMassBudget.charge; omega

/-- Full actual unfolding bounds every stopping heap and its exact successful result. -/
theorem unfold_bound (value : Value Symbol Guard) (before : State Symbol Guard) (bound : Nat)
    (stored : Stored bound before) (available : Available before value) :
    Stored (ceiling bound) (InternedFreshOrdinaryStoredSubstitution.unfold value before).state ∧
      (InternedFreshOrdinaryStoredSubstitution.unfold value before).state.nodes.next ≤ before.nodes.next + charge bound ∧
      (InternedFreshOrdinaryStoredSubstitution.unfold value before).state.edges.next ≤ before.edges.next + charge bound ∧
      ∀ result after, InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after →
        InternedValueMass.value result ≤ ceiling bound := by
  cases value with
  | mu entry body depth ordinary =>
      exact execute_bound body _ before bound stored (available.children body (by simp [children]))
        (by intro name replacement found; dsimp only at found; split at found <;> cases found; exact available)
  | empty | reference | node | union =>
      refine ⟨stored.mono (SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound),
        Nat.le_add_right _ _, Nat.le_add_right _ _, ?_⟩
      intro result after done
      cases done
      exact Nat.le_trans (InternedValueMassHeap.available before stored _ available)
        (SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound)

end MicroCFTA.SourceCurrentAllocatedProjectionResources

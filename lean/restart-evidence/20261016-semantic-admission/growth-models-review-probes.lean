import MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels

#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.derivation_exact
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.forest_exact
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.lift
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.lifted_rank
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.lifted_language
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.inventory_agreement
#check MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.derivation_exact
#check MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.forest_exact
#check MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.lift
#check MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.lifted_rank
#check MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.lifted_language
#check MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels.inventory_agreement

namespace MicroCFTA.SourceCurrentAllocatedNativeInputGrowthReviewProbes
open Language IntersectSchedule
open SourceCurrentAllocatedNativeInputGrowthModels
variable {Symbol : Type} {before after : View Symbol}
variable (inputs : FiniteInput before) (same : ViewAgreement before after inputs.valid)

-- Lifting keeps both the old domain and the same physical representative.
example : (lift inputs same).valid = inputs.valid ∧
    (lift inputs same).representative = inputs.representative := ⟨rfl, rfl⟩

-- A valid reference has an admitted Mu target in both views.
example (name : Nat) (known : inputs.valid (.ref name)) :
    (lift inputs same).valid (.mu name) := inputs.reference_valid name known

-- Old admitted reference inputs retain their exact rank, including both directions.
example (name rank : Nat) (known : inputs.valid (.ref name)) (term : Term Symbol) :
    inputAt (finiteRanks after (lift inputs same)) (.ref name) rank term ↔
      inputAt (finiteRanks before inputs) (.ref name) rank term :=
  lifted_rank inputs same (.ref name) known rank term
end MicroCFTA.SourceCurrentAllocatedNativeInputGrowthReviewProbes

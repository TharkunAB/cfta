import MicroCFTA.SourceCurrentConstrainedCapMaskCharacterization
import MicroCFTA.SourceCurrentConstrainedCapSupportedProjection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MixedNodeSupportMaskKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredGraph SourceEqualityProjectionGraph
open SourceEqualityAnnotationLanguage SourceCurrentConstrainedCapPaths
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentHereditaryConstruction (MuStored)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial uniform masks construct Required and the next signed projection at the same returned heap. -/
theorem required_then_projection (valid : Guard → Prop) (depth : Nat)
    (needed : SourceEqualityNeeded.Needed) (value : Value Symbol Guard) (before : State Symbol Guard)
    (path : List Int) (length : path.length = depth)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (closed : value.free = []) (stored : MuStored valid before)
    (uniform : ∀ path : List Int, path.length = depth → Supported valid path value) :
    ∃ required middle result after,
      RequireNode needed value before required middle ∧ Project path required middle result after ∧
      Cap valid depth required ∧ MuStored valid after ∧ Annotated valid result := by
  have bounded := SourceCurrentConstrainedCapMaskCharacterization.of_uniform valid depth value uniform
  obtain ⟨required, middle, actual, _kept, middleReady, _middleCosts, requiredAvailable,
      requiredClosed, middleStored, _providedCap, preserved, _stable⟩ :=
    SourceCurrentConstrainedCapRequiredSupport.complete valid depth needed value before
      semantic costs available closed stored bounded
  have requiredCap := SourceCurrentConstrainedCapMaskCharacterization.preserves_cap preserved bounded
  have supported := SourceCurrentConstrainedCapPaths.of_cap requiredCap path (by omega)
  obtain ⟨result, after, projection, _kept, _ready, _available, _closed, finalStored, annotated⟩ :=
    SourceCurrentConstrainedCapSupportedProjection.complete valid path required middle middleReady
      requiredAvailable requiredClosed middleStored supported
  exact ⟨required, middle, result, after, actual, projection, requiredCap, finalStored, annotated⟩

end MicroCFTA.MixedNodeSupportMaskKernels

#print axioms MicroCFTA.MixedNodeSupportMaskKernels.required_then_projection
#check @MicroCFTA.MixedNodeSupportMaskKernels.required_then_projection

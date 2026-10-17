import MicroCFTA.SourceCurrentConstrainedCapRequiredSupport
import MicroCFTA.SourceCurrentConstrainedCapSupportedProjection

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ConstrainedCapRequiredSupportKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityProjectionGraph SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPaths (Supported ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

/-- One constructed Required call retains two original masks for two later actual path calls. -/
theorem required_then_two_paths [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (needed : SourceEqualityNeeded.Needed) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (bounded : Cap valid depth value) (firstPath secondPath : List Int)
    (firstMask : Supported valid firstPath value) (secondMask : Supported valid secondPath value) :
    ∃ required middle first afterFirst second after,
      RequireNode needed value before required middle ∧ Preserves valid value required ∧
      Project firstPath required middle first afterFirst ∧ Annotated valid first ∧
      Project secondPath required afterFirst second after ∧ Annotated valid second ∧ MuStored valid after ∧
      Keeps before after ∧ Available after second ∧ second.free = [] ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel headFuel => SourceEqualityRequiredWorker.require fuel headFuel needed value before) required middle ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityProjectionWorker.project fuel readFuel secondPath required afterFirst) second after := by
  obtain ⟨required, middle, actual, kept, middleSemantic, _, output, outputClosed, middleStored, _, retained, stable⟩ :=
    SourceCurrentConstrainedCapRequiredSupport.complete valid depth needed value before semantic costs available closed stored bounded
  obtain ⟨first, afterFirst, firstActual, firstKeeps, firstSemantic, _, _, firstStored, firstAnnotation⟩ :=
    SourceCurrentConstrainedCapSupportedProjection.complete valid firstPath required middle middleSemantic output outputClosed
      middleStored (retained firstPath firstMask)
  obtain ⟨second, after, secondActual, secondKeeps, _, secondAvailable, secondClosed, secondStored, secondAnnotation⟩ :=
    SourceCurrentConstrainedCapSupportedProjection.complete valid secondPath required afterFirst firstSemantic
      (firstKeeps.available required output) outputClosed firstStored (retained secondPath secondMask)
  exact ⟨required, middle, first, afterFirst, second, after, actual, retained, firstActual, firstAnnotation,
    secondActual, secondAnnotation, secondStored, kept.trans (firstKeeps.trans secondKeeps), secondAvailable, secondClosed,
    stable, SourceEqualityProjectionWorkerComplete.node_stable secondActual⟩

/-- Arbitrary required positions retain the original selected forest mask through actual child order. -/
theorem children_then_forest [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (entries : List (Int × SourceEqualityNeeded.Needed)) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (bounded : ∀ value ∈ values, Cap valid depth value) (path : List Int) (mask : ForestSupported valid path values) :
    ∃ results middle output after,
      RequireChildren entries 0 values before results middle ∧ Language.All₂ (Preserves valid) values results ∧
      ForestSupported valid path results ∧ Forest path results middle output after ∧ Annotated valid output ∧
      MuStored valid after ∧ Keeps before after ∧ Available after output ∧ output.free = [] ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredWorker.children (SourceEqualityRequiredWorker.require fuel readFuel) entries 0 values before) results middle := by
  have childComplete : SourceEqualityRequiredListsComplete.ChildComplete (Symbol := Symbol) (Guard := Guard) entries := by
    intro index needed member value state ready input inputClosed
    exact SourceEqualityRequiredComplete.complete needed value state ready input inputClosed
  obtain ⟨results, middle, actual, kept, resultsAvailable, resultsClosed⟩ :=
    SourceEqualityRequiredListsComplete.children_complete entries childComplete 0 values before semantic.ready available closed
  have retained := SourceCurrentConstrainedCapRequiredSupport.children valid depth actual semantic costs available closed stored bounded
  have physical := SourceCurrentRequiredHeapEffects.children (fun _ => True) actual semantic costs (by intro _ _ _; trivial) available
  have resultMask := SourceCurrentConstrainedCapRequiredSupport.forest_supported valid retained.2 path mask
  obtain ⟨output, after, projected, projectionKeeps, _, outputAvailable, outputClosed, outputStored, outputAnnotation⟩ :=
    SourceCurrentConstrainedCapSupportedProjection.forest_complete valid path results middle physical.2.1
      resultsAvailable resultsClosed retained.1 resultMask
  exact ⟨results, middle, output, after, actual, retained.2, resultMask, projected, outputAnnotation,
    outputStored, kept.trans projectionKeeps, outputAvailable, outputClosed, SourceEqualityRequiredWorkerComplete.children_stable actual⟩

#print axioms required_then_two_paths
#check @required_then_two_paths
#print axioms children_then_forest
#check @children_then_forest
end MicroCFTA.ConstrainedCapRequiredSupportKernels

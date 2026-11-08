import MicroCFTA.SourceSynthesisNativeTypeSharedForce
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf

/-!
# Type origins through actual shared target leaf narrowing

The leaf forces its actual historical target before native intersection.
Every miss derives its facts before storage. A hit retains the exact stored
value. The native request transports all earlier slots to its returned heap.
The current leaf input has its own initial Type annotation and closedness.

Completed execution, structural forest routes and the input annotation
remain local premises. These laws do not establish every reached leaf's
role, trace existence, failure-prefix closure or native lazy evaluation order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedLeaf
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedSharedTargetState (State)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

/-- The same actual shared leaf retains historical targets and its annotated closed result. -/
theorem leaf (lib : Library)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : State width}
    (actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record values path input before result after)
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values)
    (routes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) values)
    (inputAvailable : Available before.checked.native.machine.heap input)
    (inputClosed : input.free = []) (inputTyped : Annotated (Origin lib) input) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  cases actual with
  | apply forced step =>
      obtain ⟨middleReady, firstExtension, targetAvailable, targetClosed, targetTyped⟩ :=
        SourceSynthesisNativeTypeSharedForce.force lib forced ready available closed routes
      cases step with
      | run trace =>
          have query := SourceSynthesisNativeTypeClosedRequests.completed lib _ middleReady.checked _ _
            targetAvailable (firstExtension.available _ inputAvailable) targetClosed inputClosed
            targetTyped inputTyped _ _ (.run trace)
          have effects := SourceCurrentAllocatedNativeTraceEffects.effects trace middleReady.checked.good
            middleReady.checked.semantic middleReady.costs (fun _ => trivial)
          exact ⟨SourceSynthesisNativeTypeSharedState.advance lib _ _ middleReady query.2.1
              effects.2.1.ready.costs query.1.extension,
            firstExtension.trans query.1.extension, query.1.physical, query.2.2, query.1.result.2⟩

end MicroCFTA.SourceSynthesisNativeTypeSharedLeaf

import MicroCFTA.SourceSynthesisNativeTypeSharedState
import MicroCFTA.SourceSynthesisNativeTypeTarget
import MicroCFTA.SourceCurrentAllocatedSharedTargetForce

/-!
# Type origins through actual shared target forcing

A hit uses the exact historical slot and returns the same whole state.
A miss derives the Type facts through the actual target before publication.
The returned checked state and merge memo supply the next shared state.
Input routes describe the captured forest. These laws do not derive the
routes for every later edited forest or assert target completion.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedForce
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedSharedTargetForce (Force)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

/-- The same completed force retains all shared certificates and returns its closed Type value. -/
theorem force (lib : Library)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {before after : Shared width} {result : Value Symbol Guard}
    (actual : Force record values path before result after) (ready : Ready lib before)
    (available : Values before.checked.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) values) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  cases actual with
  | hit present =>
      obtain ⟨known, closed, typed⟩ := ready.slots _ _ present
      exact ⟨ready, Extension.refl _, known, closed, typed⟩
  | miss absent target =>
      obtain ⟨checkedReady, costs, extension, physicalMemo, typedMemo, known, closed, typed⟩ :=
        SourceSynthesisNativeTypeTarget.target lib target ready.checked ready.costs ready.physicalMemo ready.typedMemo
          available closed (by
            intro operand included
            obtain ⟨own, member, rfl⟩ := List.mem_map.mp included
            exact routes own (List.mem_filter.mp member).1)
      exact ⟨SourceSynthesisNativeTypeSharedState.store lib _ _ _ _ _ ready checkedReady costs extension
        physicalMemo typedMemo known closed typed, extension, known, closed, typed⟩

end MicroCFTA.SourceSynthesisNativeTypeSharedForce

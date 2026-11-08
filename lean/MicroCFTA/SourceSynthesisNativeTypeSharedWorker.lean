import MicroCFTA.SourceSynthesisNativeTypeTargetWorker
import MicroCFTA.SourceSynthesisNativeTypeSharedLeaf
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerActual

/-!
# Type facts at actual executable shared target returns

The hit or miss branch supplies the exact historical target graph. Type
invariants derive readiness before the actual leaf request. No language
inventory or completed force/leaf graph is an input. The returned slot and
Merge memo keep their literal owners and values.

Successful worker returns and reached native range checks remain explicit.
These laws do not prove all reached Type routes, completion, failure-prefix
invariants, or GHC lazy execution order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedWorker
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
local notation "Force" => SourceCurrentAllocatedSharedTargetForce.Force
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

private theorem force_graph (lib : Library) (p h m s n : Nat)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {before after : State width} {result : Value Symbol Guard}
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values)
    (routes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) values)
    (ranges : SourceCurrentAllocatedSharedTargetForce.ForceRanges record values path before)
    (done : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record values path before = .done result after) :
    Force record values path before result after := by
  cases present : before.targets path with
  | some target =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force, present] at done
      cases done
      exact .hit present
  | none =>
      cases actual : SourceCurrentAllocatedTargetWorker.target p h m s n values
          (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
      | failed => simp only [SourceCurrentAllocatedSharedTargetWorker.force, present, actual] at done; cases done
      | done value checked memo =>
          simp only [SourceCurrentAllocatedSharedTargetWorker.force, present, actual] at done
          cases done
          refine .miss present ?_
          apply SourceSynthesisNativeTypeTargetWorker.target_graph lib p h m s n _ _ _ _
            ready.checked ready.costs ready.physicalMemo ready.typedMemo available closed
            ?_ (ranges present) _ _ _ actual
          intro operand included
          obtain ⟨own, member, rfl⟩ := List.mem_map.mp included
          exact routes own (List.mem_filter.mp member).1

/-- A literal force return derives its graph and all cached target Type facts. -/
theorem force (lib : Library) (p h m s n : Nat)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {before after : State width} {result : Value Symbol Guard}
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values)
    (routes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) values)
    (ranges : SourceCurrentAllocatedSharedTargetForce.ForceRanges record values path before)
    (done : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record values path before = .done result after) :
    Force record values path before result after ∧ Ready lib after ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  have graph := force_graph lib p h m s n ready available closed routes ranges done
  exact ⟨graph, SourceSynthesisNativeTypeSharedForce.force lib graph ready available closed routes⟩

/-- A literal leaf return derives its native request from the actual returned force state. -/
theorem leaf (lib : Library) (p h m s n : Nat)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : State width}
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values)
    (routes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) values)
    (inputAvailable : Available before.checked.native.machine.heap input)
    (inputClosed : input.free = []) (inputTyped : Annotated (Origin lib) input)
    (ranges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record values path input before)
    (done : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record values path input before = .done result after) :
    Leaf record values path input before result after ∧ Ready lib after ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  obtain ⟨target, middle, forced, stepped⟩ :=
    (SourceCurrentAllocatedSharedTargetWorkerActual.bind_done_iff _ _ _ _).mp
      (by simpa only [SourceCurrentAllocatedSharedTargetWorker.leaf] using done)
  obtain ⟨actualForce, middleReady, firstExtension, targetAvailable, targetClosed, _targetTyped⟩ :=
    force lib p h m s n ready available closed routes ranges.1 forced
  cases actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input))
      middle.checked with
  | yielded | failed | constraintError | blocked =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.step, actual] at stepped
      cases stepped
  | done value checked =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.step, actual] at stepped
      cases stepped
      have step := SourceCurrentAllocatedTargetWorkerNative.of_done n target input middle.checked _ checked
        middleReady.checked.good middleReady.checked.idle targetAvailable
        (firstExtension.available _ inputAvailable) targetClosed inputClosed
        (ranges.2 target middle actualForce) actual
      have graph : Leaf record values path input before result
          (SourceCurrentAllocatedSharedTargetState.advance middle checked) := .apply actualForce step
      exact ⟨graph, SourceSynthesisNativeTypeSharedLeaf.leaf lib graph ready available closed routes
        inputAvailable inputClosed inputTyped⟩

end MicroCFTA.SourceSynthesisNativeTypeSharedWorker

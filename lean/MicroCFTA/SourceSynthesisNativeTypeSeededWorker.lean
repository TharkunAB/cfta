import MicroCFTA.SourceSynthesisNativeTypeSeededProfile
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceCurrentAllocatedTargetWorkerNative

/-!
# Literal seeded returns from Type routes

Each completed projection supplies its actual operand graph. Type routes
derive readiness and closed operands at the returned prefix. The native
word check applies at the actual tail return. The first source path remains
the final seed.

Successful execution and reached word ranges remain explicit. These laws
do not prove completion, failure-state preservation, answer correctness,
an original-input resource bound, or native lazy demand correspondence.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSeededWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded FoldRanges SeededRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable {width : Nat}

private theorem operand_graph [DecidableEq (EdgeKey Symbol Guard)]
    (p h : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (result : Value Symbol Guard) (after : Checked width)
    (done : SourceCurrentAllocatedSeededWorker.operand p h path values before = .done result after) :
    Operand path values before result after := by
  cases projected : SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap with
  | done value heap =>
      simp only [SourceCurrentAllocatedSeededWorker.operand, projected] at done
      cases done
      exact .force result heap (SourceEqualityProjectionWorkerSound.forest_graph p h path values
        before.native.machine.heap result heap projected)
  | pending | unresolved | exhausted =>
      simp only [SourceCurrentAllocatedSeededWorker.operand, projected] at done
      cases done

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem ranges_cons
    {values : List (Value Symbol Guard)} {path seed : List Int} {paths : List (List Int)}
    {before : Checked width} (ranges : FoldRanges values ((path :: paths) ++ [seed]) before) :
    (∀ value middle, Operand path values before value middle →
      FoldRanges values (paths ++ [seed]) middle) ∧
    (∀ value middle tail later, Operand path values before value middle →
      Fold values (paths ++ [seed]) middle tail later →
      WordRanges (.code (SourceRecursiveIntersectionCode.requestNode
        IntersectionEmptyDomain.emptyDomain value tail)) later) := by
  cases paths with
  | nil => cases ranges with | cons rest native => exact ⟨rest, native⟩
  | cons next paths => cases ranges with | cons rest native => exact ⟨rest, native⟩

private theorem leaf_graph (n : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (ready : Ready lib before) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (SourceRecursiveIntersectionCode.requestNode
      IntersectionEmptyDomain.emptyDomain left right)) before)
    (result : Value Symbol Guard) (after : Checked width)
    (done : SourceCurrentAllocatedSeededWorker.leaf n left right before = .done result after) :
    SourceCurrentAllocatedTargetQuery.Step left right before result after := by
  cases executed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value state =>
      simp only [SourceCurrentAllocatedSeededWorker.leaf, executed] at done
      cases done
      exact SourceCurrentAllocatedTargetWorkerNative.of_done n left right before result after
        ready.good ready.idle leftAvailable rightAvailable leftClosed rightClosed ranges executed
  | yielded | failed | blocked | constraintError =>
      simp only [SourceCurrentAllocatedSeededWorker.leaf, executed] at done
      cases done

/-- A literal fold return derives its exact graph at each actual prefix state. -/
theorem fold_graph (lib : Library) (p h n : Nat)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked width) (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ seed :: paths, ForestPath (Origin lib) path values)
    (ranges : FoldRanges values (paths ++ [seed]) before)
    (result : Value Symbol Guard) (after : Checked width)
    (done : SourceCurrentAllocatedSeededWorker.fold p h n values seed paths before = .done result after) :
    Fold values (paths ++ [seed]) before result after := by
  induction paths generalizing before result after with
  | nil => exact .one (operand_graph p h seed values before result after done)
  | cons path paths ih =>
      obtain ⟨head, middle, first, rest⟩ :=
        (SourceCurrentAllocatedSeededWorkerCompletion.bind_done_iff _ _ _ _).mp
          (by simpa only [SourceCurrentAllocatedSeededWorker.fold] using done)
      obtain ⟨tail, later, tailDone, leafDone⟩ :=
        (SourceCurrentAllocatedSeededWorkerCompletion.bind_done_iff _ _ _ _).mp rest
      have firstGraph := operand_graph p h path values before head middle first
      obtain ⟨middleReady, middleCosts, firstExtension, headAvailable, headClosed, _headTyped⟩ :=
        SourceSynthesisNativeTypeOperand.operand lib firstGraph ready costs available closed
          (routes _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have tailRoutes : ∀ own ∈ seed :: paths, ForestPath (Origin lib) own values := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact routes _ List.mem_cons_self
        · exact routes own (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
      have tailAvailable := fun value member => firstExtension.available value (available value member)
      have rangeParts := ranges_cons ranges
      have tailGraph := ih middle middleReady middleCosts tailAvailable tailRoutes
        (rangeParts.1 head middle firstGraph) tail later tailDone
      have tailGraphRoutes : ∀ own ∈ paths ++ [seed], ForestPath (Origin lib) own values := by
        intro own member
        exact tailRoutes own (by simpa [List.mem_append, List.mem_cons, or_comm] using member)
      obtain ⟨tailReady, _tailCosts, tailExtension, tailResultAvailable, tailClosed, _tailTyped⟩ :=
        SourceSynthesisNativeTypeSeeded.fold lib tailGraph middleReady middleCosts
          tailAvailable closed tailGraphRoutes
      have native := leaf_graph n head tail later tailReady (tailExtension.available _ headAvailable)
        tailResultAvailable headClosed tailClosed
        (rangeParts.2 head middle tail later firstGraph tailGraph) result after leafDone
      cases native with
      | run trace =>
          cases paths with
          | nil => exact .cons firstGraph tailGraph trace
          | cons next paths => exact .cons firstGraph tailGraph trace

/-- A literal seeded return retains the source first-seed rotation and complete state. -/
theorem seeded_graph (lib : Library) (p h n : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ paths, ForestPath (Origin lib) path values)
    (ranges : SeededRanges values paths before)
    (result : Value Symbol Guard) (after : Checked width)
    (done : SourceCurrentAllocatedSeededWorker.seeded p h n values paths before = .done result after) :
    Seeded values paths before result after := by
  cases paths with
  | nil => cases done; exact .nil before
  | cons seed paths =>
      exact .nonempty (fold_graph lib p h n values seed paths before ready costs
        available closed routes ranges result after done)

/-- The same successful worker returns its exact graph and joint Type and guard facts. -/
theorem seeded (lib : Library) (p h n : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ paths, ForestPath (Origin lib) path values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (ranges : SeededRanges values paths before)
    (result : Value Symbol Guard) (after : Checked width)
    (done : SourceCurrentAllocatedSeededWorker.seeded p h n values paths before = .done result after) :
    Seeded values paths before result after ∧ Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧ Available after.native.machine.heap result ∧
      result.free = [] ∧ Annotated (Origin lib) result ∧ GuardHeap (Origin lib) after.native.machine.heap := by
  have graph := seeded_graph lib p h n values paths before ready costs available closed routes ranges result after done
  exact ⟨graph, SourceSynthesisNativeTypeSeededProfile.seeded lib graph ready costs available closed routes guards⟩

end MicroCFTA.SourceSynthesisNativeTypeSeededWorker

import MicroCFTA.SourcePruningEnumerationParentProjectionMerge
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
import MicroCFTA.SourceCurrentAllocatedSeededQuery

/-!
# Projectability through actual checked shared and seeded targets

This draft follows the actual recorded worker endpoints.
It does not assert completion of an arbitrary native prefix.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetQuery
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual checked target query retains projectability at its same complete native endpoint. -/
theorem Receipt.projection_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left right result : Value Symbol Guard}
    {before after : Checked width} {memos : Memos}
    (receipt : Receipt formulas solver inventory left right before result after memos)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases receipt.actual with
  | run trace =>
      exact SourcePruningEnumerationNativeQueryProjectionHeap.node_query_heap
        ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ before after result _ good heap trace

end MicroCFTA.SourceCurrentAllocatedTargetQuery

namespace MicroCFTA.SourcePruningEnumerationSharedTargetProjectionHeap
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetComplete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "SharedState" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual operand projects first and then merges at that same reached heap. -/
theorem operand_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {output : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo output after saved memos final)
    (ready : ClassReady before) (available : Values before.native.machine.heap values)
    (stored : Stored before.native.machine.heap memo) (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have middleHeap := SourcePruningEnumerationPathProjectionHeap.forest_heap projection.graph
    ready.semantic ready.costs available heap
  cases merged.actual with
  | done actual =>
      exact SourcePruningEnumerationAllocatedMergeProjectionHeap.call_heap actual
        (SourceCurrentAllocatedConjunctionMemo.ready middle projection.ready.good projection.ready.semantic projection.ready.costs)
        (stored.grows projection.effects.keeps) projection.available middleHeap

/-- Actual ordered target reads retain the same full reached states and stored merge table. -/
theorem fold_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedTargetGraph.Fold values seed paths before memo result after saved}
    (reads : FoldReads formulas solver actual memos final) (ready : ClassReady before)
    (available : Values before.native.machine.heap values) (stored : Stored before.native.machine.heap memo)
    (heap : Heap before.native.machine.heap) :
    ClassReady after ∧ Values after.native.machine.heap values ∧ Stored after.native.machine.heap saved ∧ Heap after.native.machine.heap := by
  induction reads with
  | nil receipt => exact ⟨receipt.ready, receipt.originals, receipt.stored, operand_heap receipt ready available stored heap⟩
  | cons receipt remaining query ih =>
      obtain ⟨laterReady, laterValues, laterStored, laterHeap⟩ := ih receipt.ready receipt.originals receipt.stored
        (operand_heap receipt ready available stored heap)
      exact ⟨query.ready, fun value member => query.effects.keeps.available value (laterValues value member),
        laterStored.grows query.effects.keeps, query.projection_heap laterReady.good laterHeap⟩

/-- Actual first-seeded target construction retains projectability at its own returned checked heap. -/
theorem target_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedTargetGraph.Target values paths before memo result after saved}
    (reads : TargetReads formulas solver actual memos final) (ready : ClassReady before)
    (available : Values before.native.machine.heap values) (stored : Stored before.native.machine.heap memo)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases reads with
  | nil => exact heap
  | cons reads => exact (fold_heap reads ready available stored heap).2.2.2

/-- A real shared force reuses its slot or follows the same actual target miss reads. -/
theorem force_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : SharedState width} {result : Value Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedSharedTargetForce.Force record values path before result after}
    (reads : SourceCurrentAllocatedSharedTargetForce.Reads formulas solver actual memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (heap : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap := by
  cases reads with
  | hit => exact heap
  | miss _ reads =>
      exact target_heap reads ready.checked
        (fun value member => ready.captured.available value (known value member)) ready.stored heap

/-- The actual forced target precedes the recorded native leaf query at its returned heap. -/
theorem leaf_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path} {input result : Value Symbol Guard}
    {before after : SharedState width} {memos final : Memos}
    {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record values path input before result after}
    (reads : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (heap : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap := by
  cases reads with
  | apply first query =>
      have middleHeap := force_heap first.reads ready known heap
      exact query.projection_heap first.ready.checked.good middleHeap

end MicroCFTA.SourcePruningEnumerationSharedTargetProjectionHeap

namespace MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "SharedState" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual full leaf receipt derives its edge-record projectability from its genuine initial class state. -/
theorem Receipt.projection_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory initialInventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path} {input result : Value Symbol Guard}
    {before after : SharedState width} {memos final : Memos}
    (receipt : Receipt formulas solver inventory record values base path input before result after memos final)
    (ready : SharedReady formulas solver initialInventory record values base before) (known : Values base values)
    (heap : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap :=
  SourcePruningEnumerationSharedTargetProjectionHeap.leaf_heap receipt.reads ready known heap

end MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf


namespace MicroCFTA.SourcePruningEnumerationSeededProjectionHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedSeededQuery
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]
/-- Actual projection retains the complete projectability heap before any checked intersection. -/
theorem operand_heap
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {value : Value Symbol Guard} (actual : Operand path values before value after)
    (ready : Ready (physical before)) (available : Values before.native.machine.heap values)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | force returned projected =>
      exact SourcePruningEnumerationPathProjectionHeap.forest_heap projected ready.semantic ready.costs available heap

variable [DecidableEq Symbol]

private theorem fold_complete_heap
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (heap : Heap before.native.machine.heap) :
    ∃ result after, Fold values paths before result after ∧ Good after ∧
      Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] ∧
      Heap after.native.machine.heap := by
  induction paths generalizing before with
  | nil => cases ranges
  | cons path paths ih =>
      cases paths with
      | nil =>
          obtain ⟨result, after, actual, good, effects, extension, returnedScopes, idle, resident, closed⟩ :=
            operand_complete unconstrained anchor anchorSemantic anchorReady path values before
              good ready scopes idle available growth (supported path (by simp))
          exact ⟨result, after, .one actual, good, effects, extension, returnedScopes, idle, resident, closed,
            operand_heap actual ready available heap⟩
      | cons next paths =>
          cases ranges with
          | cons rest native =>
              obtain ⟨value, middle, first, middleGood, firstEffects, firstExtension, middleScoped,
                middleIdle, valueAvailable, valueClosed⟩ := operand_complete unconstrained anchor anchorSemantic anchorReady
                  path values before good ready scopes idle available growth (supported path (by simp))
              have middleHeap := operand_heap first ready available heap
              obtain ⟨tail, later, remaining, laterGood, remainingEffects, remainingExtension, laterScoped,
                laterIdle, tailAvailable, tailClosed, laterHeap⟩ := ih middle (rest value middle first)
                  middleGood firstEffects.ready middleScoped middleIdle
                  (fun value member => firstEffects.keeps.available value (available value member))
                  (grows_trans growth firstEffects.keeps.growth)
                  (fun path member => supported path (List.mem_cons_of_mem _ member)) middleHeap
              have valueLater := remainingEffects.keeps.available value valueAvailable
              have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original value later.native.machine.heap
                laterGood.native.machine.1.coherent valueLater valueClosed
              have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original tail later.native.machine.heap
                laterGood.native.machine.1.coherent tailAvailable tailClosed
              obtain ⟨fuel, result, after, receipt, afterIdle, resultClosed⟩ :=
                SourceCurrentAllocatedNativeScopeCompletion.initial_complete (fun _ _ => true) later laterGood
                  laterScoped remainingEffects.ready.semantic laterIdle value tail leftOriginal rightOriginal
                  valueLater tailAvailable valueClosed tailClosed (native value middle tail later first remaining)
              have checked := SourceCurrentAllocatedNativeTraceEffects.effects receipt.trace laterGood
                remainingEffects.ready.semantic remainingEffects.ready.costs (fun _ => trivial)
              have afterHeap := SourcePruningEnumerationNativeQueryProjectionHeap.node_query_heap
                ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ later after result fuel laterGood laterHeap receipt.trace
              exact ⟨result, after, .cons first remaining receipt.trace, checked.1,
                firstEffects.trans (remainingEffects.trans checked.2.1),
                firstExtension.trans (remainingExtension.trans checked.2.2), receipt.scopedCache,
                afterIdle, receipt.result, resultClosed, afterHeap⟩

/-- The original reached ranges derive projectability at the exact supplied fold endpoint. -/
theorem fold_heap
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Fold values paths before result after)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  obtain ⟨chosen, reached, completed, _good, _effects, _extension, _scoped, _idle, _resident, _closed, current⟩ :=
    fold_complete_heap unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready scopes idle
      available growth supported heap
  obtain ⟨rfl, rfl⟩ := actual.unique completed
  exact current

/-- The actual first-seed rotation retains projectability at its complete returned checked state. -/
theorem seeded_heap
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Seeded values paths before result after)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | nil => exact heap
  | nonempty fold =>
      apply fold_heap unconstrained anchor anchorSemantic anchorReady fold ranges good ready scopes idle available growth
      · intro path member
        exact supported path (by simpa [List.mem_append, List.mem_cons, or_comm] using member)
      · exact heap

end MicroCFTA.SourcePruningEnumerationSeededProjectionHeap

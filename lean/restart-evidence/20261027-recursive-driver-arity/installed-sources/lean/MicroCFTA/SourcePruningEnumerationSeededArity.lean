import MicroCFTA.SourceCurrentAllocatedSeededQuery
import MicroCFTA.SourcePruningEnumerationProjectionArity
import MicroCFTA.SourcePruningEnumerationNativeQueryArity

/-!
# Arity through actual checked first-seeded queries

Projection retains arity before the actual recursive tail.
The completed native call checks all records created after that tail.
Original range and support contracts derive each current physical state.
-/
namespace MicroCFTA.SourcePruningEnumerationSeededArity
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
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]
/-- Actual projection retains the complete arity heap before any checked intersection. -/
theorem operand_heap
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {value : Value Symbol Guard} (actual : Operand path values before value after)
    (ready : Ready (physical before)) (available : Values before.native.machine.heap values)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | force returned projected =>
      exact SourcePruningEnumerationProjectionArity.forest_heap projected ready.semantic ready.costs available heap

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
              have afterHeap := SourcePruningEnumerationNativeQueryArity.node_query_heap
                ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ later after result fuel laterGood laterHeap receipt.trace
              exact ⟨result, after, .cons first remaining receipt.trace, checked.1,
                firstEffects.trans (remainingEffects.trans checked.2.1),
                firstExtension.trans (remainingExtension.trans checked.2.2), receipt.scopedCache,
                afterIdle, receipt.result, resultClosed, afterHeap⟩

/-- The original reached ranges derive arity at the exact supplied fold endpoint. -/
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

/-- The actual first-seed rotation retains arity at its complete returned checked state. -/
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

end MicroCFTA.SourcePruningEnumerationSeededArity

import MicroCFTA.SourceCurrentActualMergeOperandOrigins
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.InternedFreshOrdinaryCosts

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.ActualMergeOperandOriginKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceCurrentMergePositiveRowOrigins (Raw Writer)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Node" => Value Symbol Guard
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def top : Guard := SourceEqualityConstraintConstructors.top
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) top [],.mk ("loop",.top) top [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("pair",.top) own [recursive,recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def before := SourceCurrentAllocatedPartialInitialization.checked 8 Cache.emptyState heap
private noncomputable def cold := SourceCurrentAllocatedTargetWorker.operand 8 8 32 8 [0] [value]
  before SourceCurrentMemoMergeGraph.empty
private noncomputable def saved := cold.memo
private def row : EdgeValue Symbol Guard := match nodeEdges value with
  | first :: _ => first
  | [] => (run (makeEdge ("pair",.top) own []) heap).1
private def records := (SourceEqualityClassOrder.recordsOf [[[0],[1]]]).getD []

private theorem built_done : built = .done value heap := by cbv
private theorem cold_done : cold = .done value cold.state saved := by cbv
private theorem warm_done : SourceCurrentAllocatedTargetWorker.operand 8 8 1 0 [0] [value] cold.state saved =
    .done value cold.state saved := by cbv
private theorem selected : row ∈ nodeEdges value := by cbv; exact List.mem_cons_self
private theorem own_positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) := by cbv
private theorem records_live : records ≠ [] := by cbv; intro impossible; cases impossible
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression value heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  exact InternedFreshOrdinaryCosts.closed_heap expression
private theorem available : Available heap value :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built_done
private theorem initial_raw : Raw SourceCurrentAllocatedMerge.literalClear top (SourceCurrentMemoMergeGraph.empty : SourceCurrentMemoMergeGraph.Memo Symbol Guard) := by
  intro key entry impossible
  cases impossible
private theorem stored : SourceCurrentMemoMergeEffects.Stored heap SourceCurrentMemoMergeGraph.empty :=
  SourceCurrentMemoMergeEffects.stored_empty heap
private theorem returned_effect : SourceCurrentMemoMergeEffects.Effect heap cold.state.native.machine.heap ∧
    SourceCurrentMemoMergeEffects.Stored cold.state.native.machine.heap saved ∧
    Available cold.state.native.machine.heap value := by
  have actual : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear 32 8 value
      (SourceCurrentAllocatedNativeEffects.physical before) SourceCurrentMemoMergeGraph.empty =
      .done value (SourceCurrentAllocatedNativeEffects.physical cold.state) saved := by cbv
  have graph := (SourceCurrentAllocatedMergeWorkerSound.call_sound actual).graph
  exact ⟨(SourceCurrentMemoMergeEffects.call_effects graph semantic costs stored available).1,
    (SourceCurrentMemoMergeEffects.call_effects graph semantic costs stored available).2.1,
    (SourceCurrentMemoMergeEffects.call_effects graph semantic costs stored available).2.2.1⟩
private theorem final_values : InternedNestedProvenance.Values cold.state.native.machine.heap [value] := by
  intro input member
  cases List.mem_singleton.mp member
  exact returned_effect.2.2
private theorem values : InternedNestedProvenance.Values heap [value] := by
  intro input member
  cases List.mem_singleton.mp member
  exact available

private theorem kernel :
    ∃ (source : Syntax Symbol Guard) (input : Node) (initialHeap : State Symbol Guard)
      (checked after : Checked 8) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
      (selectedRow : EdgeValue Symbol Guard) (classes : List SourceEqualityClassOrder.Record),
      InternedFreshOrdinaryConstruction.build source [] empty = .done input initialHeap ∧
      checked.native.machine.heap = initialHeap ∧
      SourceEqualityRequiredSemanticCache.SemanticReady initialHeap ∧ InternedFreshOrdinaryCostHeap.Heap initialHeap ∧
      Available initialHeap input ∧
      SourceCurrentAllocatedTargetWorker.operand 8 8 32 8 [0] [input] checked SourceCurrentMemoMergeGraph.empty =
        .done input after memo ∧
      SourceCurrentAllocatedTargetWorker.operand 8 8 1 0 [0] [input] after memo = .done input after memo ∧
      selectedRow ∈ nodeEdges input ∧
      SourceEqualityPhysicalPayload.own selectedRow.entry.key.constraint = .ok (some classes) ∧ classes ≠ [] ∧
      Raw SourceCurrentAllocatedMerge.literalClear top memo ∧
      ∃ (projected : Node) (middle : Checked 8),
        SourceEqualityProjectionGraph.Forest [0] [input] after.native.machine.heap projected middle.native.machine.heap ∧
        Writer SourceCurrentAllocatedMerge.literalClear top projected input ∧
        ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard), (nodeEdges projected)[sourceIndex]? = some original ∧
          selectedRow.entry.key.symbol = original.entry.key.symbol ∧
          selectedRow.entry.key.constraint = original.entry.key.constraint ∧
          (selectedRow = original ∨ ∃ start current finish final,
            SourceCurrentMemoMergeGraph.Run SourceCurrentAllocatedMerge.literalClear top
              (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request original.children)
              start current selectedRow.children finish final) := by
  obtain ⟨raw,_origin⟩ :=
    SourceCurrentActualMergeOperandOrigins.operand cold_done semantic costs stored values initial_raw
      row selected records own_positive records_live
  obtain ⟨_raw,projected,middle,_projection,_merge,projection,writer,origin⟩ :=
    SourceCurrentActualMergeOperandOrigins.operand warm_done returned_effect.1.semantic returned_effect.1.costs returned_effect.2.1 final_values raw
      row selected records own_positive records_live
  exact ⟨expression,value,heap,before,cold.state,saved,row,records,built_done,rfl,semantic,costs,available,
    cold_done,warm_done,selected,own_positive,records_live,raw,projected,middle,projection,writer,origin⟩

theorem cold_warm :
    ∃ (source : Syntax Symbol Guard) (input : Node) (initialHeap : State Symbol Guard)
      (checked after : Checked 8) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
      (selectedRow : EdgeValue Symbol Guard) (classes : List SourceEqualityClassOrder.Record),
      InternedFreshOrdinaryConstruction.build source [] empty = .done input initialHeap ∧
      checked.native.machine.heap = initialHeap ∧
      SourceEqualityRequiredSemanticCache.SemanticReady initialHeap ∧ InternedFreshOrdinaryCostHeap.Heap initialHeap ∧
      Available initialHeap input ∧
      SourceCurrentAllocatedTargetWorker.operand 8 8 32 8 [0] [input] checked SourceCurrentMemoMergeGraph.empty =
        .done input after memo ∧
      SourceCurrentAllocatedTargetWorker.operand 8 8 1 0 [0] [input] after memo = .done input after memo ∧
      selectedRow ∈ nodeEdges input ∧
      SourceEqualityPhysicalPayload.own selectedRow.entry.key.constraint = .ok (some classes) ∧ classes ≠ [] ∧
      Raw SourceCurrentAllocatedMerge.literalClear top memo ∧
      ∃ (projected : Node) (middle : Checked 8),
        SourceEqualityProjectionGraph.Forest [0] [input] after.native.machine.heap projected middle.native.machine.heap ∧
        Writer SourceCurrentAllocatedMerge.literalClear top projected input ∧
        ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard), (nodeEdges projected)[sourceIndex]? = some original ∧
          selectedRow.entry.key.symbol = original.entry.key.symbol ∧
          selectedRow.entry.key.constraint = original.entry.key.constraint ∧
          (selectedRow = original ∨ ∃ start current finish final,
            SourceCurrentMemoMergeGraph.Run SourceCurrentAllocatedMerge.literalClear top
              (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request original.children)
              start current selectedRow.children finish final) := kernel

end MicroCFTA.ActualMergeOperandOriginKernels

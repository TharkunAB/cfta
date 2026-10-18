import MicroCFTA.SourceCurrentTargetMergeHistory
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.TargetMergeHistoryKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionThunks
open SourceCurrentMergePositiveRowOrigins (Raw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def top : Guard := SourceEqualityConstraintConstructors.top
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) top [],.mk ("loop",.top) top [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("pair",.top) top [recursive,recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def allocation := SourceEqualityConstraintAllocation.construct top.equalities Cache.emptyState
private def allocated := match allocation.1 with | .ok value => value | .error _ => .contradiction
private def before : Checked 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
private noncomputable def cold := SourceCurrentAllocatedTargetWorker.target 8 8 32 8 16
  [value,value] [[0],[1]] before SourceCurrentMemoMergeGraph.empty
private noncomputable def output : Node := match cold with | .done value .. => value | .failed .. => .empty
private noncomputable def warm := SourceCurrentAllocatedTargetWorker.target 8 8 1 0 8
  [value,value] [[0],[1]] cold.state cold.memo
private noncomputable def warmOutput : Node := match warm with | .done value .. => value | .failed .. => .empty
private theorem built_done : built = .done value heap := by cbv
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready before := by
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [top] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
      (show allocation = (.ok allocated,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [top] := by
    intro guard member
    simpa only [expression,recursive,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.nil_append,List.append_nil,or_false,or_self] using member
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid
    expression covered value heap built_done).1
private theorem good : SourceCurrentNativeOperationHeap.Good before :=
  ⟨⟨initial_ready.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,
    initial_ready.good.heap,initial_ready.good.operations,initial_ready.good.fields,initial_ready.semantic,initial_ready.costs⟩
private theorem available : InternedNestedProvenance.Values heap [value,value] := by
  intro input member
  have same : input = value := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  subst input
  exact (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built_done
private theorem initial_raw : Raw SourceCurrentAllocatedMerge.literalClear top
    (SourceCurrentMemoMergeGraph.empty : SourceCurrentMemoMergeGraph.Memo Symbol Guard) := by
  intro key entry impossible
  cases impossible
private theorem cold_done : cold = .done output cold.state cold.memo := by
  have tag : (match cold with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : cold with
  | done value after saved => simp only [output,actual,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedTargetWorker.Outcome.memo]
  | failed fault after saved => rw [actual] at tag; cases tag
private theorem warm_done : warm = .done warmOutput warm.state warm.memo := by
  have tag : (match warm with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : warm with
  | done value after saved => simp only [warmOutput,actual,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedTargetWorker.Outcome.memo]
  | failed fault after saved => rw [actual] at tag; cases tag
private theorem kernel :
    ∃ (source : Syntax Symbol Guard) (input : Node) (initialHeap : State Symbol Guard)
      (before : Checked 8) (coldResult warmResult : Node) (middle after : Checked 8)
      (saved final : SourceCurrentMemoMergeGraph.Memo Symbol Guard),
      InternedFreshOrdinaryConstruction.build source [] empty = .done input initialHeap ∧
      before.native.machine.heap = initialHeap ∧ SourceCurrentNativeOperationHeap.Good before ∧
      InternedNestedProvenance.Values initialHeap [input,input] ∧
      SourceCurrentAllocatedTargetWorker.target 8 8 32 8 16 [input,input] [[0],[1]] before
        SourceCurrentMemoMergeGraph.empty = .done coldResult middle saved ∧
      SourceCurrentAllocatedTargetWorker.target 8 8 1 0 8 [input,input] [[0],[1]] middle saved =
        .done warmResult after final ∧
      Raw SourceCurrentAllocatedMerge.literalClear top saved ∧
      Raw SourceCurrentAllocatedMerge.literalClear top final := by
  have stored := SourceCurrentMemoMergeEffects.stored_empty heap
  have first := SourceCurrentTargetMergeHistory.target cold_done good stored available initial_raw
  obtain ⟨effect,retained,_returned⟩ := SourceCurrentLowerOperationInvariants.target cold_done good stored available
  have last := SourceCurrentTargetMergeHistory.target warm_done effect.good retained
    (fun input member => effect.keeps.available input (available input member)) first
  exact ⟨expression,value,heap,before,output,warmOutput,cold.state,warm.state,cold.memo,warm.memo,
    built_done,rfl,good,available,cold_done,warm_done,first,last⟩

theorem cold_warm :
    ∃ (source : Syntax Symbol Guard) (input : Node) (initialHeap : State Symbol Guard)
      (before : Checked 8) (coldResult warmResult : Node) (middle after : Checked 8)
      (saved final : SourceCurrentMemoMergeGraph.Memo Symbol Guard),
      InternedFreshOrdinaryConstruction.build source [] empty = .done input initialHeap ∧
      before.native.machine.heap = initialHeap ∧ SourceCurrentNativeOperationHeap.Good before ∧
      InternedNestedProvenance.Values initialHeap [input,input] ∧
      SourceCurrentAllocatedTargetWorker.target 8 8 32 8 16 [input,input] [[0],[1]] before
        SourceCurrentMemoMergeGraph.empty = .done coldResult middle saved ∧
      SourceCurrentAllocatedTargetWorker.target 8 8 1 0 8 [input,input] [[0],[1]] middle saved =
        .done warmResult after final ∧
      Raw SourceCurrentAllocatedMerge.literalClear top saved ∧
      Raw SourceCurrentAllocatedMerge.literalClear top final := kernel

end MicroCFTA.TargetMergeHistoryKernels

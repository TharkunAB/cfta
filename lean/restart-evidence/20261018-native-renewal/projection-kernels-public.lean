import MicroCFTA.SourceCurrentActualTargetOperandSourceOrigins
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentConstrainedCapMergeJointEffects
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.SourceEqualityNormalizationReceipt
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.NativeRenewalProjectionKernels
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityProjectionGraph EndpointStatefulGateTrace
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [],.top⟩
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def tau : Syntax Symbol Guard := .binder false (.node [.mk ("rec",.top) plain [.var 0]])
private def pair : Syntax Symbol Guard := .node [.mk ("positive",.top) own [leaf,leaf]]
private def expression : Syntax Symbol Guard :=
  .node [.mk ("first",.top) plain [tau],.mk ("second",.top) plain [pair]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def tauBuilt := InternedFreshOrdinaryConstruction.build tau [] empty
private def mu : Node := ((nodeEdges root)[0]?.getD (run (makeEdge ("unused",.top) plain []) heap).1).children[0]?.getD .empty
private def sourcePair : Node := ((nodeEdges root)[1]?.getD (run (makeEdge ("unused",.top) plain []) heap).1).children[0]?.getD .empty
private def row : Row := (nodeEdges sourcePair)[0]?.getD (run (makeEdge ("unused",.top) plain []) heap).1
private def next : Node := row.children[0]?.getD .empty
private def called := SourceEqualityProjectionWorker.project 3 4 [0] root heap
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after := match called with | .done _ state => state | _ => heap
private theorem built_done : built = .done root heap := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem normal : SourceCurrentRequiredUnionNormal.UnionNormal heap := by
  simpa only [heap,built] using SourceCurrentRequiredUnionNormal.build expression [] empty
    (by intro key value found; cases found)
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem accepted : source mu = true := by
  obtain ⟨value,state,done,_,annotated⟩ := SourceEqualityAnnotationConstruction.closed
    (fun guard : Guard => guard = plain) tau
    (by simp [tau,SourceEqualityAnnotationConstruction.Allowed,SourceEqualityAnnotationConstruction.ManyAllowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed])
  have tauDone : tauBuilt = .done mu tauBuilt.state := by cbv
  have same := (InternedNestedConstruction.Outcome.done.inj (done.symm.trans tauDone)).1
  have original : SourceEqualityAnnotationLanguage.Annotated (fun guard : Guard => guard = plain) mu := same ▸ annotated
  apply SourceCurrentHereditaryUnconstrained.unconstrained
  exact SourceCurrentHereditaryUnconstrained.annotated_mono
    (first := fun guard : Guard => guard = plain) (second := Plain)
    (fun guard same => by
      cases same
      simp [SourceMemoGate.plain,SourceCompactGuards.sourceEqualities,SourceCompactGuards.positiveNormalized,plain]) original
private theorem gate : NodeTrace source reaches [0] root heap false heap := by
  have yes := accepted
  conv at yes => lhs; arg 1; cbv
  conv => arg 4; cbv
  apply NodeTrace.branches
  · cbv
  · apply EdgesTrace.next
    · apply ChildTrace.present
      · rfl
      · apply NodeTrace.closed
        · exact yes
        · cbv
    · apply EdgesTrace.next
      · apply ChildTrace.present
        · rfl
        · exact .finite (by cbv)
      · exact .nil
private theorem completed : called = .done result after := by cbv
private theorem actual : Project [0] root heap result after :=
  SourceEqualityProjectionWorkerSound.project_graph 3 4 [0] root heap result after completed
private theorem selected : row ∈ nodeEdges result := by
  exact List.mem_of_getElem? (show (nodeEdges result)[0]? = some row by cbv)
private theorem positive : ¬ Plain row.entry.key.constraint := by
  have fields : row.entry.key.constraint = own := by cbv
  rw [fields]
  simp [SourceMemoGate.plain,SourceCompactGuards.sourceEqualities,SourceCompactGuards.positiveNormalized,own]

private def before := SourceCurrentAllocatedPartialInitialization.checked 8 Cache.emptyState heap
private def emptyMemo : SourceCurrentMemoMergeGraph.Memo Symbol Guard := SourceCurrentMemoMergeGraph.empty
private def cold := SourceCurrentAllocatedTargetWorker.operand 3 4 32 8 [0,0] [root] before emptyMemo
private def output : Node := match cold with | .done value _ _ => value | _ => .empty
private def saved := cold.memo
private def records : List SourceEqualityClassOrder.Record := (SourceEqualityClassOrder.recordsOf [[[0],[1]]]).getD []
private theorem cold_done : cold = .done output cold.state saved := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases actual : cold with
  | done _value after memo => simp only [output,saved,actual,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedTargetWorker.Outcome.memo]
  | failed => rw [actual] at tag; cases tag
private theorem warm_done : SourceCurrentAllocatedTargetWorker.operand 3 4 1 0 [0,0] [root] cold.state saved =
    .done output cold.state saved := by cbv
private theorem output_member : row ∈ nodeEdges output := by
  exact List.mem_of_getElem? (show (nodeEdges output)[0]? = some row by cbv)
private theorem own_positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) := by cbv
private theorem nonempty_records : records ≠ [] := by cbv; intro impossible; cases impossible
private theorem initialValues : InternedNestedProvenance.Values heap [root] :=
  fun _value member => (List.mem_singleton.mp member) ▸ available
private theorem initialStored : SourceCurrentMemoMergeEffects.Stored heap emptyMemo :=
  SourceCurrentMemoMergeEffects.stored_empty heap
private theorem initialRaw : SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear
    SourceEqualityConstraintConstructors.top emptyMemo := by intro key entry absent; cases absent
private theorem pathGate : PathTrace source reaches [root] [0,0] heap false heap := .child (.present rfl gate)
private theorem merge_effect {input : Node} {start finish : SourceEqualityNativeDemand.State 8} {current final}
    (actual : SourceCurrentAllocatedMerge.Merge SourceCurrentAllocatedMerge.literalClear input start current
      output finish final)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady start.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap start.native.machine.heap)
    (stored : SourceCurrentMemoMergeEffects.Stored start.native.machine.heap current)
    (available : Available start.native.machine.heap input)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain start.native.machine.heap) :
    SourceCurrentMemoMergeEffects.Effect start.native.machine.heap finish.native.machine.heap ∧
    SourceCurrentMemoMergeEffects.Stored finish.native.machine.heap final ∧
    SourceCurrentConstrainedCapGuardHeap.Heap Plain finish.native.machine.heap := by
  cases actual with
  | done called =>
    have effects := SourceCurrentMemoMergeEffects.call_effects called.graph semantic costs stored available
    exact ⟨effects.1,effects.2.1,SourceCurrentConstrainedCapMergeJointEffects.call_heap Plain called.graph
      semantic costs stored available guards⟩
private theorem returned_effect :
    SourceCurrentMemoMergeEffects.Effect heap cold.state.native.machine.heap ∧
    SourceCurrentMemoMergeEffects.Stored cold.state.native.machine.heap saved ∧
    SourceCurrentConstrainedCapGuardHeap.Heap Plain cold.state.native.machine.heap := by
  have actual := SourceCurrentAllocatedTargetWorkerSound.operand_sound 3 4 32 8 [0,0] [root] before
    emptyMemo output cold.state saved cold_done
  cases actual with
  | force projected merged =>
    have first := SourceEqualityProjectionCosts.forest_effects projected semantic costs initialValues
    have middleGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain projected semantic costs initialValues guards
    have last := merge_effect merged first.2.1 first.2.2.1 (initialStored.grows first.1) first.2.2.2 middleGuards
    exact ⟨⟨first.1.trans last.1.keeps,last.1.semantic,last.1.costs⟩,last.2.1,last.2.2⟩
private theorem finalValues : InternedNestedProvenance.Values cold.state.native.machine.heap [root] :=
  fun value member => returned_effect.1.keeps.available value (initialValues value member)

private def Claim : Prop :=
  built = .done root heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
  SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap root ∧
  SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
  PathTrace source reaches [root] [0,0] heap false heap ∧
  SourceEqualityRequiredGraph.Recursive mu ∧ source mu = true ∧
  cold = .done output cold.state saved ∧
  SourceCurrentAllocatedTargetWorker.operand 3 4 1 0 [0,0] [root] cold.state saved = .done output cold.state saved ∧
  row ∈ nodeEdges output ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
  SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top saved ∧
  ∃ (projected sourceValue : Node) (middle : SourceEqualityNativeDemand.State 8) (sourceIndex : Nat) (original : Row),
    SourceCurrentAllocatedTargetWorker.projection 3 4 [0,0] [root] cold.state saved = .done projected middle saved ∧
    SourceCurrentAllocatedTargetWorker.merge 1 0 projected middle saved = .done output cold.state saved ∧
    SourceCurrentMergePositiveRowOrigins.Writer SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top projected output ∧
    [root][0]? = some sourceValue ∧ (nodeEdges projected)[sourceIndex]? = some original ∧
    Project [0] sourceValue cold.state.native.machine.heap projected middle.native.machine.heap ∧
    SourceCurrentPositiveProjectionSourceRoute.Route [0] sourceValue original ∧
    row.entry.key.symbol = original.entry.key.symbol ∧ row.entry.key.constraint = original.entry.key.constraint ∧
    (∀ child ∈ original.children, InternedValueMass.value child < InternedValueMass.value sourceValue) ∧
    (row = original ∨ ∃ start current finish final,
      SourceCurrentMemoMergeGraph.Run SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top
        (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request original.children)
        start current row.children finish final)
private theorem checked : Claim := by
  obtain ⟨raw,_⟩ := SourceCurrentActualTargetOperandSourceOrigins.operand 0 [0] [root]
    before cold.state emptyMemo saved output cold_done semantic costs initialStored initialValues initialRaw guards
    heap heap pathGate semantic normal initialValues (grows_refl _) row output_member records own_positive nonempty_records
  obtain ⟨_,projected,middle,sourceValue,sourceIndex,original,projection,merge,_forest,writer,
      atIndex,found,project,route,symbol,guard,smaller,children⟩ :=
    SourceCurrentActualTargetOperandSourceOrigins.operand 0 [0] [root] cold.state cold.state saved saved output
      warm_done returned_effect.1.semantic returned_effect.1.costs returned_effect.2.1 finalValues raw returned_effect.2.2
      heap heap pathGate semantic normal initialValues returned_effect.1.keeps.growth row output_member records own_positive nonempty_records
  exact ⟨built_done,semantic,normal,available,guards,pathGate,by cbv,accepted,cold_done,warm_done,output_member,
    own_positive,nonempty_records,raw,projected,sourceValue,middle,sourceIndex,original,projection,merge,writer,
    atIndex,found,project,route,symbol,guard,smaller,children⟩

/-- Actual cold and warm target operands retain an indexed ordinary input row beside a recursive read. -/
theorem cold_warm_original_anchors :
  built = .done root heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
  SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap root ∧
  SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
  PathTrace source reaches [root] [0,0] heap false heap ∧
  SourceEqualityRequiredGraph.Recursive mu ∧ source mu = true ∧
  cold = .done output cold.state saved ∧
  SourceCurrentAllocatedTargetWorker.operand 3 4 1 0 [0,0] [root] cold.state saved = .done output cold.state saved ∧
  row ∈ nodeEdges output ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
  SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top saved ∧
  ∃ (projected sourceValue : Node) (middle : SourceEqualityNativeDemand.State 8) (sourceIndex : Nat) (original : Row),
    SourceCurrentAllocatedTargetWorker.projection 3 4 [0,0] [root] cold.state saved = .done projected middle saved ∧
    SourceCurrentAllocatedTargetWorker.merge 1 0 projected middle saved = .done output cold.state saved ∧
    SourceCurrentMergePositiveRowOrigins.Writer SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top projected output ∧
    [root][0]? = some sourceValue ∧ (nodeEdges projected)[sourceIndex]? = some original ∧
    Project [0] sourceValue cold.state.native.machine.heap projected middle.native.machine.heap ∧
    SourceCurrentPositiveProjectionSourceRoute.Route [0] sourceValue original ∧
    row.entry.key.symbol = original.entry.key.symbol ∧ row.entry.key.constraint = original.entry.key.constraint ∧
    (∀ child ∈ original.children, InternedValueMass.value child < InternedValueMass.value sourceValue) ∧
    (row = original ∨ ∃ start current finish final,
      SourceCurrentMemoMergeGraph.Run SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top
        (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request original.children)
        start current row.children finish final) := checked
end
end MicroCFTA.NativeRenewalProjectionKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

#check @MicroCFTA.NativeRenewalProjectionKernels.cold_warm_original_anchors
#print MicroCFTA.NativeRenewalProjectionKernels.cold_warm_original_anchors
#print axioms MicroCFTA.NativeRenewalProjectionKernels.cold_warm_original_anchors

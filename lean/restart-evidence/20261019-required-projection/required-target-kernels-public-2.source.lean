import MicroCFTA.SourceCurrentRequiredTargetOperandOrigins
import MicroCFTA.SourceCurrentActualMergeOperandOrigins
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentMuEndpoint
import MicroCFTA.SourceEqualityNormalizationReceipt
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RequiredTargetKernels
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
private def expression : Syntax Symbol Guard := .node [.mk ("positive",.top) own [tau,leaf]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def paths : EqualityNormalize.Class := [[0],[0,0,0]]
private def required := SourceEqualityRequiredExecution.requireAll 8 8
  (paths.map (List.map Int.ofNat)) [root] heap
private def prepared : List Node := match required with | .done values _ => values | _ => []
private def requiredHeap : Heap := match required with | .done _ state => state | _ => heap
private def oldRow : Row := (nodeEdges root)[0]?.getD (run (makeEdge ("unused",.top) plain []) heap).1
private def preparedRoot : Node := prepared[0]?.getD .empty
private def preparedRow : Row := (nodeEdges preparedRoot)[0]?.getD oldRow
private def before := SourceCurrentAllocatedPartialInitialization.checked 8 Cache.emptyState requiredHeap
private def emptyMemo : SourceCurrentMemoMergeGraph.Memo Symbol Guard := SourceCurrentMemoMergeGraph.empty
private def called := SourceCurrentAllocatedTargetWorker.operand 4 8 32 8 [0] prepared before emptyMemo
private def result : Node := match called with | .done value _ _ => value | _ => .empty
private def saved := called.memo
private def resultRow : Row := (nodeEdges result)[0]?.getD oldRow
private def records : List SourceEqualityClassOrder.Record := (SourceEqualityClassOrder.recordsOf [[[0],[1]]]).getD []
private theorem built_done : built = .done root heap := by cbv
private theorem required_done : required = .done prepared requiredHeap := by cbv
private theorem original_gate : SourceCurrentMuEndpoint.classMeets true source reaches 8 [root] paths heap =
    .done (some false) heap := by cbv
private theorem changed : preparedRow.children ≠ oldRow.children := by
  intro same
  have first := congrArg (fun values => values[0]?.map Value.referenceOf) same
  cbv at first
  cases first
private theorem positive : SourceEqualityPhysicalPayload.own resultRow.entry.key.constraint = .ok (some records) := by cbv
private theorem actual_done : called = .done result called.state saved := by
  have tag : (match called with | .done .. => true | _ => false) = true := by cbv
  cases actual : called with
  | done value state memo => simp only [actual,result,saved,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedTargetWorker.Outcome.memo]
  | failed => rw [actual] at tag; cases tag
private theorem nonempty : records ≠ [] := by cbv; intro impossible; cases impossible
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem normal : SourceCurrentRequiredUnionNormal.UnionNormal heap := by
  simpa only [heap,built] using SourceCurrentRequiredUnionNormal.source expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem available : InternedNestedProvenance.Values heap [root] := by
  intro value member
  cases List.mem_singleton.mp member
  exact (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem gate : ClassTrace source reaches [root] paths heap false heap :=
  class_trace_of_done source reaches 8 [root] paths heap false heap
    (by simpa only [SourceCurrentMuEndpoint.primary_class] using original_gate)
private theorem raw : SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear
    SourceEqualityConstraintConstructors.top emptyMemo := by intro key entry absent; cases absent
private theorem row_member : resultRow ∈ nodeEdges result := by
  exact List.mem_of_getElem? (show (nodeEdges result)[0]? = some resultRow by cbv)
private theorem root_projection {values : List Node} {value result : Node} {before after : Heap}
    (actual : Forest [0] values before result after) (found : values[0]? = some value) : result = value := by
  cases actual with
  | missing absent => simp only [select,Int.reduceLT,ite_false,Int.toNat_zero] at absent; rw [found] at absent; cases absent
  | selected chosen body =>
    cases body with
    | root =>
      have equal : values[0]? = some result := by simpa only [select,Int.reduceLT,ite_false,Int.toNat_zero] using chosen
      exact Option.some.inj (equal.symm.trans found)
private theorem route_root {value : Node} {row : Row}
    (route : SourceCurrentPositiveProjectionSourceRoute.Route [] value row) : row ∈ nodeEdges value := by
  cases route with
  | root entry rows depth free position row found => exact List.mem_of_getElem? found

private theorem checked :
    ∃ (projected : Node) (middle : SourceEqualityNativeDemand.State 8),
      SourceCurrentAllocatedTargetWorker.projection 4 8 [0] prepared before emptyMemo = .done projected middle emptyMemo ∧
      SourceCurrentAllocatedTargetWorker.merge 32 8 projected middle emptyMemo = .done result called.state saved ∧
      SourceCurrentMergePositiveRowOrigins.Writer SourceCurrentAllocatedMerge.literalClear
        SourceEqualityConstraintConstructors.top projected result ∧
      SourceCurrentPositiveProjectionSourceRoute.Route [] root oldRow ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin oldRow preparedRow ∧
      Language.All₂ SourceCurrentRequiredRowOrigins.Origin oldRow.children preparedRow.children ∧
      resultRow.entry.key.symbol = preparedRow.entry.key.symbol ∧
      resultRow.entry.key.constraint = preparedRow.entry.key.constraint ∧
      (resultRow = preparedRow ∨ ∃ start current finish final,
        SourceCurrentMemoMergeGraph.Run SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top
          (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request preparedRow.children)
          start current resultRow.children finish final) := by
  obtain ⟨_,projected,middle,sourceValue,preparedValue,sourceIndex,returnedSource,original,
      projectionDone,mergeDone,graph,writer,originalFound,preparedFound,rowFound,_,route,fields,origins,symbol,guard,_,children⟩ :=
    SourceCurrentRequiredTargetOperandOrigins.operand 0 [] paths [root] prepared heap requiredHeap before called.state
      emptyMemo saved result required_done actual_done rfl semantic normal costs guards available
      (SourceCurrentMemoMergeEffects.stored_empty _) raw heap heap gate semantic available
      (grows_refl heap) (by simp [paths]) resultRow row_member records positive nonempty
  have sourceSame : sourceValue = root := (Option.some.inj originalFound).symm
  subst sourceValue
  have originalSame : original = oldRow := by
    have member := route_root route
    rw [show nodeEdges root = [oldRow] by cbv] at member
    exact List.mem_singleton.mp member
  subst original
  have projectedSame := root_projection graph (show prepared[0]? = some preparedRoot by cbv)
  have rowSame : returnedSource = preparedRow := by
    have member := List.mem_of_getElem? rowFound
    rw [projectedSame,show nodeEdges preparedRoot = [preparedRow] by cbv] at member
    exact List.mem_singleton.mp member
  subst returnedSource
  exact ⟨projected,middle,projectionDone,mergeDone,writer,route,fields,origins,symbol,guard,children⟩

private theorem checked_witness :
    ∃ (program : Syntax Symbol Guard) (input : Node) (initial preparedHeap : Heap) (prepared : List Node)
      (before after : SourceEqualityNativeDemand.State 8) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
      (result : Node) (original preparedRow resultRow : Row),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input initial ∧
      ClassTrace source reaches [input] [[0],[0,0,0]] initial false initial ∧
      SourceEqualityRequiredExecution.requireAll 8 8 [[0],[0,0,0]] [input] initial = .done prepared preparedHeap ∧
      before.native.machine.heap = preparedHeap ∧
      original ∈ nodeEdges input ∧ original.children ≠ preparedRow.children ∧
      SourceCurrentAllocatedTargetWorker.operand 4 8 32 8 [0] prepared before SourceCurrentMemoMergeGraph.empty =
        .done result after saved ∧ resultRow ∈ nodeEdges result ∧
      SourceEqualityPhysicalPayload.own resultRow.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
      ∃ (projected : Node) (middle : SourceEqualityNativeDemand.State 8),
        SourceCurrentAllocatedTargetWorker.projection 4 8 [0] prepared before SourceCurrentMemoMergeGraph.empty =
          .done projected middle SourceCurrentMemoMergeGraph.empty ∧
        SourceCurrentAllocatedTargetWorker.merge 32 8 projected middle SourceCurrentMemoMergeGraph.empty =
          .done result after saved ∧
        SourceCurrentMergePositiveRowOrigins.Writer SourceCurrentAllocatedMerge.literalClear
          SourceEqualityConstraintConstructors.top projected result ∧
        SourceCurrentPositiveProjectionSourceRoute.Route [] input original ∧
        SourceCurrentRequiredGuardOrigins.RowOrigin original preparedRow ∧
        Language.All₂ SourceCurrentRequiredRowOrigins.Origin original.children preparedRow.children ∧
        resultRow.entry.key.symbol = preparedRow.entry.key.symbol ∧
        resultRow.entry.key.constraint = preparedRow.entry.key.constraint ∧
        (resultRow = preparedRow ∨ ∃ start current finish final,
          SourceCurrentMemoMergeGraph.Run SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top
            (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request preparedRow.children)
            start current resultRow.children finish final) := by
  exact ⟨expression,root,heap,requiredHeap,prepared,before,called.state,saved,result,oldRow,preparedRow,resultRow,
    built_done,gate,required_done,rfl,
    List.mem_of_getElem? (show (nodeEdges root)[0]? = some oldRow by cbv),
    Ne.symm changed,actual_done,row_member,positive,nonempty,checked⟩


/-- A source-built Required call changes positive-row children and supplies their original target provenance. -/
theorem actual_changed_children :
    ∃ (program : Syntax Symbol Guard) (input : Node) (initial preparedHeap : Heap) (prepared : List Node)
      (before after : SourceEqualityNativeDemand.State 8) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
      (result : Node) (original preparedRow resultRow : Row),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input initial ∧
      ClassTrace source reaches [input] [[0],[0,0,0]] initial false initial ∧
      SourceEqualityRequiredExecution.requireAll 8 8 [[0],[0,0,0]] [input] initial = .done prepared preparedHeap ∧
      before.native.machine.heap = preparedHeap ∧
      original ∈ nodeEdges input ∧ original.children ≠ preparedRow.children ∧
      SourceCurrentAllocatedTargetWorker.operand 4 8 32 8 [0] prepared before SourceCurrentMemoMergeGraph.empty =
        .done result after saved ∧ resultRow ∈ nodeEdges result ∧
      SourceEqualityPhysicalPayload.own resultRow.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
      ∃ (projected : Node) (middle : SourceEqualityNativeDemand.State 8),
        SourceCurrentAllocatedTargetWorker.projection 4 8 [0] prepared before SourceCurrentMemoMergeGraph.empty =
          .done projected middle SourceCurrentMemoMergeGraph.empty ∧
        SourceCurrentAllocatedTargetWorker.merge 32 8 projected middle SourceCurrentMemoMergeGraph.empty =
          .done result after saved ∧
        SourceCurrentMergePositiveRowOrigins.Writer SourceCurrentAllocatedMerge.literalClear
          SourceEqualityConstraintConstructors.top projected result ∧
        SourceCurrentPositiveProjectionSourceRoute.Route [] input original ∧
        SourceCurrentRequiredGuardOrigins.RowOrigin original preparedRow ∧
        Language.All₂ SourceCurrentRequiredRowOrigins.Origin original.children preparedRow.children ∧
        resultRow.entry.key.symbol = preparedRow.entry.key.symbol ∧
        resultRow.entry.key.constraint = preparedRow.entry.key.constraint ∧
        (resultRow = preparedRow ∨ ∃ start current finish final,
          SourceCurrentMemoMergeGraph.Run SourceCurrentAllocatedMerge.literalClear SourceEqualityConstraintConstructors.top
            (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request preparedRow.children)
            start current resultRow.children finish final) := checked_witness

end
end MicroCFTA.RequiredTargetKernels


set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.RequiredTargetKernels.actual_changed_children
#print MicroCFTA.RequiredTargetKernels.actual_changed_children
#print axioms MicroCFTA.RequiredTargetKernels.actual_changed_children

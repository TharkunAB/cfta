import MicroCFTA.SourceCurrentRequiredPrimaryOrigins
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
private theorem same_fields : SourceCurrentRequiredGuardOrigins.RowOrigin oldRow preparedRow := by cbv
private theorem positive : SourceEqualityPhysicalPayload.own resultRow.entry.key.constraint = .ok (some records) := by cbv
private theorem actual_done : called = .done result called.state saved := by
  have tag : (match called with | .done .. => true | _ => false) = true := by cbv
  cases actual : called with
  | done value state memo => simp only [actual,result,saved,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedTargetWorker.Outcome.memo]
  | failed => rw [actual] at tag; cases tag
private theorem nonempty : records ≠ [] := by cbv; intro impossible; cases impossible
end
end MicroCFTA.RequiredTargetKernels

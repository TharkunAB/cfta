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

namespace MicroCFTA.EmptyForestMuBoundary
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
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("pair",.top) own [.var 0,.var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def mu : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def body : Node := (InternedProbeProvenance.children mu)[0]?.getD .empty
private def called := SourceEqualityProjectionWorker.forest 3 0 [] [mu] heap
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after := match called with | .done _ heap => heap | _ => heap
private def row : Row := (nodeEdges result)[0]?.getD (run (makeEdge ("unused",.top) plain []) heap).1
private def bodyRow : Row := (nodeEdges body)[0]?.getD row
private def records := (SourceEqualityClassOrder.recordsOf [[[0],[1]]]).getD []
private theorem built_done : built = .done mu heap := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression mu heap built_done
private theorem available : Available heap mu :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result mu heap built_done
private theorem normal : SourceCurrentRequiredUnionNormal.UnionNormal heap := by
  simpa only [heap,built] using SourceCurrentRequiredUnionNormal.build expression [] empty
    SourceCurrentRequiredUnionNormal.empty
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem completed : called = .done result after := by cbv
private theorem graph : Forest [] [mu] heap result after :=
  SourceEqualityProjectionWorkerSound.forest_graph 3 0 [] [mu] heap result after completed
private theorem selected : row ∈ nodeEdges result :=
  List.mem_of_getElem? (show (nodeEdges result)[0]? = some row by cbv)
private theorem nonempty_records : records ≠ [] := by cbv; intro impossible; cases impossible
private theorem own_positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) := by cbv
private theorem rejected : source mu = false := by
  have no : ¬ source mu = true := by
    intro accepted
    have reached : InternedSourceCrush.Reaches [mu] body := .child mu body
      (.root mu List.mem_cons_self) (by cbv; exact List.mem_cons_self)
    have present : bodyRow ∈ nodeEdges body :=
      List.mem_of_getElem? (show (nodeEdges body)[0]? = some bodyRow by cbv)
    have emptyOwn := SourceCurrentGatePlainRegion.reached_empty heap mu
      semantic.ready.semantic.1.normal.facts.coherent available accepted body reached bodyRow present
    have originalOwn : SourceEqualityPhysicalPayload.own bodyRow.entry.key.constraint = .ok (some records) := by cbv
    rw [originalOwn] at emptyOwn
    exact nonempty_records (Option.some.inj (Except.ok.inj emptyOwn))
  cases actual : source mu with
  | false => rfl
  | true => exact (no actual).elim
private theorem no_route : ¬ SourceCurrentPositiveProjectionSourceRoute.Route [] mu row := by
  intro route
  have recursive : SourceEqualityRequiredGraph.Recursive mu := by cbv
  cases route with
  | root => cases recursive

private def Claim : Prop :=
  built = .done mu heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
  SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap mu ∧
  SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
  PathTrace source reaches [mu] [] heap false heap ∧ source mu = false ∧
  called = .done result after ∧ Forest [] [mu] heap result after ∧
  row ∈ nodeEdges result ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
  row.children[0]? = some mu ∧ ¬ SourceCurrentPositiveProjectionSourceRoute.Route [] mu row ∧
  ¬ InternedValueMass.value mu < InternedValueMass.value mu
private theorem checked : Claim :=
  ⟨built_done,semantic,normal,available,guards,.empty,rejected,completed,graph,selected,own_positive,
    nonempty_records,by cbv,no_route,Nat.lt_irrefl _⟩

/-- Empty forest gating can expose a positive constrained Mu row with a continuation equal to its source. -/
theorem empty_path_does_not_give_route :
  built = .done mu heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
  SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap mu ∧
  SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
  PathTrace source reaches [mu] [] heap false heap ∧ source mu = false ∧
  called = .done result after ∧ Forest [] [mu] heap result after ∧
  row ∈ nodeEdges result ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
  row.children[0]? = some mu ∧ ¬ SourceCurrentPositiveProjectionSourceRoute.Route [] mu row ∧
  ¬ InternedValueMass.value mu < InternedValueMass.value mu := checked
end
end MicroCFTA.EmptyForestMuBoundary

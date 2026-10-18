import MicroCFTA.SourceCurrentPositiveProjectionSourceRoute
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.SourceEqualityNormalizationReceipt
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.PositiveProjectionRouteKernels
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

private def Claim : Prop :=
  built = .done root heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
  SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap root ∧
  SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
  NodeTrace source reaches [0] root heap false heap ∧
  SourceEqualityRequiredGraph.Recursive mu ∧ source mu = true ∧
  called = .done result after ∧ Project [0] root heap result after ∧
  (nodeEdges result).length = 2 ∧ row ∈ nodeEdges result ∧ ¬ Plain row.entry.key.constraint ∧
  SourceCurrentPositiveProjectionSourceRoute.Route [0] root row ∧
  row.children[0]? = some next ∧ InternedValueMass.value next < InternedValueMass.value root
private theorem checked : Claim := by
  have route := SourceCurrentPositiveProjectionSourceRoute.positive [0] root heap heap heap after result gate
    semantic normal available (grows_refl _) semantic costs available guards actual row selected positive
  have found : row.children[0]? = some next := by cbv
  exact ⟨built_done,semantic,normal,available,guards,gate,by cbv,accepted,completed,actual,
    by cbv,selected,positive,route,found,route.mass_lt next (List.mem_of_getElem? found)⟩

/-- A real mixed projection keeps the positive ordinary row beside an accepted recursive read. -/
theorem mixed_ordinary_and_recursive :
  built = .done root heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
  SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap root ∧
  SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
  NodeTrace source reaches [0] root heap false heap ∧
  SourceEqualityRequiredGraph.Recursive mu ∧ source mu = true ∧
  called = .done result after ∧ Project [0] root heap result after ∧
  (nodeEdges result).length = 2 ∧ row ∈ nodeEdges result ∧ ¬ Plain row.entry.key.constraint ∧
  SourceCurrentPositiveProjectionSourceRoute.Route [0] root row ∧
  row.children[0]? = some next ∧ InternedValueMass.value next < InternedValueMass.value root := checked
end
end MicroCFTA.PositiveProjectionRouteKernels

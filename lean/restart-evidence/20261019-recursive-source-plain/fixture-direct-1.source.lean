import MicroCFTA.SourceCurrentRecursiveSourcePlain
import MicroCFTA.SourceEqualityRequiredWorkerSound
import MicroCFTA.SourceEqualityRequiredExecution
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# Actual Required exposure at an original false gate

The source contains a positive wrapper row and a plain used Mu child.
An empty requirement keeps the exact source occurrence. A nonempty
requirement exposes that Mu and moves it below an ordinary row.
Only the original source gate is used.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.RecursiveSourcePlainKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredGraph SourceCurrentRequiredRowOrigins
open SourceCurrentClassRecursiveValueOrigins SourceEqualityAnnotationLanguage EndpointStatefulGateTrace
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
private def positive : Guard := ⟨some [[[0],[1]]],.top⟩
private def tau : Syntax Symbol Guard := .binder false (.node [.mk ("rec",.top) plain [.var 0]])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("wrapper",.top) positive [tau,.node [.mk ("leaf",.top) plain []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def mu : Node := (children root)[0]?.getD .empty
private def leafValue : Node := (children root)[1]?.getD .empty
private def row : Row := (nodeEdges root)[0]?.getD (run (makeEdge ("unused",.top) plain []) heap).1
private def rootEntry := match root with | .node entry _ _ _ => entry | _ => (Cache.intern empty.nodes .empty).1
private def needed := SourceEqualityNeeded.build [[0,0]]
private def called := SourceEqualityRequiredWorker.require 8 8 needed root heap
private def prepared : Node := match called with | .done value _ => value | _ => .empty
private def after : Heap := match called with | .done _ state => state | _ => heap
private def preparedRow : Row := (nodeEdges prepared)[0]?.getD row
private def exposed : Node := preparedRow.children[0]?.getD .empty
private def inner : Row := (nodeEdges exposed)[0]?.getD row
private theorem built_done : built = .done root heap := by cbv
private theorem root_shape : root = .node rootEntry [row] root.depth root.free := by cbv
private theorem shapes : row.children = [mu,leafValue] ∧ preparedRow.children = [exposed,leafValue] ∧
    inner.children = [mu] ∧ (nodeEdges root)[0]? = some row ∧
    (nodeEdges prepared)[0]? = some preparedRow ∧ (nodeEdges exposed)[0]? = some inner ∧
    Recursive mu ∧ (match mu with | .mu _ _ depth ordinary =>
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    source mu = true ∧ source leafValue = true ∧ row.entry.key.constraint = positive ∧
    SourceMemoGate.plain positive = false := by cbv; trivial
private theorem actual_done : called = .done prepared after := by cbv
private theorem original_gate : EndpointStatefulGate.nodeMeets source reaches 8 [0,0] root heap =
    .done (some false) heap := by cbv
private theorem gate : NodeTrace source reaches [0,0] root heap false heap :=
  node_trace_of_done source reaches 8 [0,0] root heap false heap original_gate
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem normal : SourceCurrentRequiredUnionNormal.UnionNormal heap := by
  simpa only [heap,built] using SourceCurrentRequiredUnionNormal.source expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem occurrence : Occurs root [0] mu := by
  rw [root_shape]
  exact .child 0 0 row mu rfl (by rw [shapes.1]; rfl) (.root _)
private theorem prepared_occurrence : Occurs prepared [0,0] mu := by
  have lift {parent : Node} {row : Row} {child : Node} {path : List Nat} {target : Node}
      (selected : (nodeEdges parent)[0]? = some row) (chosen : row.children[0]? = some child)
      (rest : Occurs child path target) : Occurs parent (0::path) target := by
    cases parent with
    | node entry edges depth free => exact .child 0 0 row child selected chosen rest
    | empty | reference | union | mu => cases selected
  exact lift shapes.2.2.2.2.1 (by rw [shapes.2.1]; rfl)
    (lift shapes.2.2.2.2.2.1 (by rw [shapes.2.2.1]; rfl) (.root _))
private theorem no_original : ¬ Occurs root [0,0] mu := by
  intro present
  rw [root_shape] at present
  cases present with
  | child rowIndex childIndex parent child selected chosen rest =>
    have sameRow : parent = row := List.mem_singleton.mp (List.mem_of_getElem? selected)
    subst parent
    rw [shapes.1] at chosen
    have sameChild : child = mu := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using chosen.symm
    subst child
    have recursive := shapes.2.2.2.2.2.2.1
    cases rest with
    | child => cases recursive
private theorem safe : ExposureSafe needed root := by
  rw [root_shape]
  apply ExposureSafe.ordinary
  intro parent member index childNeeded _ child selected
  have sameRow : parent = row := List.mem_singleton.mp member
  subst parent
  have included : child = mu ∨ child = leafValue := by
    simpa only [shapes.1,List.mem_cons,List.not_mem_nil,or_false] using List.mem_of_getElem? selected
  apply ExposureSafe.accepted
  rcases included with rfl | rfl
  · exact shapes.2.2.2.2.2.2.2.2.1
  · exact shapes.2.2.2.2.2.2.2.2.2.1
private theorem actual : RequireNode needed root heap prepared after :=
  SourceEqualityRequiredWorkerSound.require_graph 8 8 needed root heap prepared after actual_done
private theorem related : Origin root prepared :=
  SourceCurrentRequiredRowOrigins.node actual semantic costs available guards safe

private theorem checked_witness :
    built = .done root heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
    SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap root ∧
    SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧ row.entry.key.constraint = positive ∧
    SourceMemoGate.plain positive = false ∧ Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    NodeTrace source reaches [0,0] root heap false heap ∧
    SourceEqualityRequiredWorker.require 8 8 SourceEqualityNeeded.empty root heap = .done root heap ∧
    RequireNode SourceEqualityNeeded.empty root heap root heap ∧ Origin root root ∧ Occurs root [0] mu ∧
    called = .done prepared after ∧ RequireNode needed root heap prepared after ∧ Origin root prepared ∧
    preparedRow.children = [exposed,leafValue] ∧ inner.children = [mu] ∧
    Occurs prepared [0,0] mu ∧ ¬ Occurs root [0,0] mu ∧
    (Occurs root [0] mu ∨ Annotated Plain mu) ∧ Annotated Plain mu := by
  have sourceCase := SourceCurrentRecursiveSourcePlain.origin (Origin.identity root) occurrence
    shapes.2.2.2.2.2.2.1
  have requiredPlain := SourceCurrentRecursiveSourcePlain.required semantic normal available related prepared_occurrence
    shapes.2.2.2.2.2.2.1 [] gate
  exact ⟨built_done,semantic,normal,available,guards,shapes.2.2.2.2.2.2.2.2.2.2.1,
    shapes.2.2.2.2.2.2.2.2.2.2.2,shapes.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.1,gate,
    rfl,.identity,.identity _,occurrence,actual_done,actual,related,shapes.2.1,shapes.2.2.1,prepared_occurrence,
    no_original,sourceCase,requiredPlain⟩

/-- Actual Required calls exercise retained source and plain exposure at one original false gate. -/
theorem source_and_exposure :
    built = .done root heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
    SourceCurrentRequiredUnionNormal.UnionNormal heap ∧ Available heap root ∧
    SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧ row.entry.key.constraint = positive ∧
    SourceMemoGate.plain positive = false ∧ Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    NodeTrace source reaches [0,0] root heap false heap ∧
    SourceEqualityRequiredWorker.require 8 8 SourceEqualityNeeded.empty root heap = .done root heap ∧
    RequireNode SourceEqualityNeeded.empty root heap root heap ∧ Origin root root ∧ Occurs root [0] mu ∧
    called = .done prepared after ∧ RequireNode needed root heap prepared after ∧ Origin root prepared ∧
    preparedRow.children = [exposed,leafValue] ∧ inner.children = [mu] ∧
    Occurs prepared [0,0] mu ∧ ¬ Occurs root [0,0] mu ∧
    (Occurs root [0] mu ∨ Annotated Plain mu) ∧ Annotated Plain mu := checked_witness
end MicroCFTA.RecursiveSourcePlainKernels

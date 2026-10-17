import MicroCFTA.SourceCurrentOuterExecutionAncestry
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
set_option linter.all true
set_option maxErrors 5
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option cbv.maxSteps 1000000
namespace MicroCFTA.OuterExecutionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionKernel InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq Node := by classical exact inferInstance
private def plain : Guard := ⟨some [],.top⟩
private def rejectedGuard : Guard := ⟨none,.top⟩
private def program : Syntax Symbol Guard :=
  .node [.mk ("root",.top) rejectedGuard [.node [.mk ("leaf",.top) plain []]]]
private def built := InternedFreshOrdinaryConstruction.build program [] empty
private def original : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def before := SourceCurrentAllocatedPartialInitialization.caller 4 Cache.emptyState heap
private def inherited := SourceCurrentAllocatedPartialInitialization.emptyValue Cache.emptyState
private def request : NodeRequest := ⟨inherited,original⟩
private def running := (beginNode request before).2.2
private def sourceRow := ((nodeEdges original)[0]?).getD (run (makeEdge ("unused",.top) plain []) heap).1
private def edgeRequest : EdgeRequest := ⟨inherited,sourceRow⟩
private def edgeRunning := (beginEdge edgeRequest running).2.2
private def sentinel := (SourceCurrentAllocatedMkEdge.reject sourceRow.entry.key.symbol edgeRunning.checked).1
private def parentReturn := finishEdge 0 sentinel
  (advance edgeRunning (SourceCurrentAllocatedMkEdge.reject sourceRow.entry.key.symbol edgeRunning.checked).2
    edgeRunning.fourth edgeRunning.merge)
private noncomputable def combined :=
  match (SourceCurrentAllocatedInheritedPrefix.run sentinel.entry.key.constraint inherited parentReturn.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def prefixed := SourceCurrentAllocatedPartialGraph.prefixState parentReturn sentinel inherited
private noncomputable def descended := SourceCurrentAllocatedPartialGraph.descend prefixed combined 0
private noncomputable def child : NodeRequest := ⟨descended.1,.empty⟩
private noncomputable def childRunning := (beginNode child descended.2).2.2
private noncomputable def childAfter := finishNode 1 .empty childRunning
private def start : Phase 4 := .node 5 request before
private noncomputable def atChild : Phase 4 := .node 2 child descended.2
private noncomputable def inChild : Phase 4 := .body 2 child childRunning
private noncomputable def afterChild : Phase 4 := .walk 2 combined 1 [] childAfter
private theorem rootStarted : beginNode request before = (0,.evaluate request,running) := by cbv
private theorem edgeStarted : beginEdge edgeRequest running = (0,.evaluate edgeRequest,edgeRunning) := by cbv
private theorem childStarted : beginNode child descended.2 = (1,.evaluate child,childRunning) := by cbv
private theorem rejected : SourceEqualityMkEdgeAllocation.contradictory sourceRow.entry.key.constraint = true := by cbv
private theorem edgeDone : edgeCall 3 0 0 0 0 0 0 0 0 0 0 edgeRequest running = .done sentinel parentReturn := by
  cbv
private theorem sentinelChildren : sentinel.children = [.empty] := by cbv
private theorem prefixDone :
    (SourceCurrentAllocatedInheritedPrefix.run sentinel.entry.key.constraint inherited parentReturn.checked.operations).1 =
      .ok (some combined) := by cbv
private theorem reached : Reached 0 0 0 0 0 0 0 0 0 0 start inChild := by
  have first : Reached 0 0 0 0 0 0 0 0 0 0 start (.body 5 request running) :=
    .snoc (.refl _) (.node_evaluate rootStarted)
  have rows : Reached 0 0 0 0 0 0 0 0 0 0 start (.rows 4 inherited [sourceRow] running) :=
    .snoc first (.body_rows (by cbv))
  have edge : Reached 0 0 0 0 0 0 0 0 0 0 start (.descendants 3 inherited sentinel parentReturn) :=
    .snoc rows (.rows_edge edgeDone)
  have children : Reached 0 0 0 0 0 0 0 0 0 0 start (.children 3 combined [.empty] prefixed) := by
    simpa only [sentinelChildren,prefixed] using Reached.snoc edge (Step.descendants_children prefixDone)
  have walked : Reached 0 0 0 0 0 0 0 0 0 0 start (.walk 3 combined 0 [.empty] prefixed) :=
    .snoc children (.children_walk (by intro impossible; cbv at impossible; cases impossible))
  have demanded : Reached 0 0 0 0 0 0 0 0 0 0 start atChild := .snoc walked .walk_head
  exact .snoc demanded (.node_evaluate childStarted)
private theorem childDone : nodeCall 2 0 0 0 0 0 0 0 0 0 0 child descended.2 = .done .empty childAfter := by
  rw [nodeCall,childStarted]
  simp only [nodeBody,child,Outcome.bind,childAfter]
private theorem returned : Reached 0 0 0 0 0 0 0 0 0 0 start afterChild := by
  have first : Reached 0 0 0 0 0 0 0 0 0 0 start (.body 5 request running) :=
    .snoc (.refl _) (.node_evaluate rootStarted)
  have rows : Reached 0 0 0 0 0 0 0 0 0 0 start (.rows 4 inherited [sourceRow] running) :=
    .snoc first (.body_rows (by cbv))
  have edge : Reached 0 0 0 0 0 0 0 0 0 0 start (.descendants 3 inherited sentinel parentReturn) :=
    .snoc rows (.rows_edge edgeDone)
  have children : Reached 0 0 0 0 0 0 0 0 0 0 start (.children 3 combined [.empty] prefixed) :=
    by simpa only [sentinelChildren,prefixed] using Reached.snoc edge (Step.descendants_children prefixDone)
  have walked : Reached 0 0 0 0 0 0 0 0 0 0 start (.walk 3 combined 0 [.empty] prefixed) :=
    .snoc children (.children_walk (by intro impossible; cbv at impossible; cases impossible))
  exact .snoc walked (.walk_tail childDone)
private noncomputable def busyEntry : Phase 4 := .walk 1 inherited 0 [original] running
private noncomputable def busyDescent := SourceCurrentAllocatedPartialGraph.descend running inherited 0
private noncomputable def busyRequest : NodeRequest := ⟨busyDescent.1,original⟩
private noncomputable def busyAfter := busyDescent.2
private theorem busyStarted : beginNode busyRequest busyAfter = (0,.busy,busyAfter) := by cbv
private theorem busyDone : walk 1 0 0 0 0 0 0 0 0 0 0 inherited 0 [original] running =
    .failed (.nodeMemo 0 .busy) busyAfter := by
  rw [walk,nodeCall,busyStarted]
  rfl
/-- A literal warm caller failure derives its own nonempty dispatch prefix at the exact changed operation state. -/
theorem warm_busy_dispatch :
    built = .done original heap ∧ Available heap original ∧
    beginNode request before = (0,.evaluate request,running) ∧
    walk 1 0 0 0 0 0 0 0 0 0 0 inherited 0 [original] running = .failed (.nodeMemo 0 .busy) busyAfter ∧
    busyAfter.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    busyRequest.key = request.key ∧
    SourceCurrentOuterActiveAncestry.run 0 0 0 0 0 0 0 0 0 0 busyEntry = .failed (.nodeMemo 0 .busy) busyAfter ∧
    Dispatch 0 0 0 0 0 0 0 0 0 0 busyEntry 0 busyAfter := by
  have builtDone : built = .done original heap := by cbv
  have verified := InternedFreshOrdinaryFacts.closed_verified program
  have protocol := SourceCurrentAllocatedPartialFrames.beginNode_frame request before
    (SourceCurrentAllocatedPartialFrames.initial_protocol _ _ _)
  rw [rootStarted] at protocol
  have valid : NodeValid running := protocol.valid.nodes
  have actual : SourceCurrentOuterActiveAncestry.run 0 0 0 0 0 0 0 0 0 0 busyEntry =
      .failed (.nodeMemo 0 .busy) busyAfter := by
    simp only [SourceCurrentOuterActiveAncestry.run,busyEntry,busyDone,Outcome.bind]
  exact ⟨builtDone,verified.result _ _ builtDone,rootStarted,busyDone,by cbv,by cbv,actual,failed valid actual⟩
/-- Actual rejected-parent and completed-child equations derive complete ancestry without supplied graphs. -/
theorem actual_prefixes :
    built = .done original heap ∧ Available heap original ∧
    Reached 0 0 0 0 0 0 0 0 0 0 start inChild ∧
    childRunning.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    childRunning.nodeResults.cells 1 = some ⟨child,.evaluating⟩ ∧
    (∀ handle owner, childRunning.nodeResults.cells handle = some ⟨owner,.evaluating⟩ →
      Ancestor 0 0 0 0 0 0 0 0 0 0 start inChild handle owner) ∧
    Reached 0 0 0 0 0 0 0 0 0 0 start afterChild ∧
    childAfter.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    childAfter.nodeResults.cells 1 = some ⟨child,.returned .empty⟩ ∧
    (∀ handle owner, childAfter.nodeResults.cells handle = some ⟨owner,.evaluating⟩ →
      Ancestor 0 0 0 0 0 0 0 0 0 0 start afterChild handle owner) := by
  have builtDone : built = .done original heap := by cbv
  have verified := InternedFreshOrdinaryFacts.closed_verified program
  have active := reached.owners (SourceCurrentAllocatedPartialFrames.initial_protocol _ _ _).nodes
    (fun _ _ impossible => by cases impossible)
  have remaining := returned.owners (SourceCurrentAllocatedPartialFrames.initial_protocol _ _ _).nodes
    (fun _ _ impossible => by cases impossible)
  exact ⟨builtDone,verified.result _ _ builtDone,reached,by cbv,by cbv,active,returned,by cbv,by cbv,remaining⟩
end MicroCFTA.OuterExecutionKernels
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

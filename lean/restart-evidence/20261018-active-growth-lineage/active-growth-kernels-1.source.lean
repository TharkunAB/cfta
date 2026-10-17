import MicroCFTA.SourceCurrentOuterExecutionGrowth
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
set_option linter.all true
set_option maxErrors 5
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option cbv.maxSteps 1000000
namespace MicroCFTA.ActiveGrowthKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
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
  have called := nodeCall_busy 0 0 0 0 0 0 0 0 0 0 0 busyRequest busyAfter busyAfter 0 busyStarted
  simp only [busyRequest,busyAfter,busyDescent] at called
  simp only [walk,called,Outcome.bind,busyAfter,busyDescent]

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

private theorem busyPrefix : Reached 0 0 0 0 0 0 0 0 0 0 busyEntry (.node 0 busyRequest busyAfter) :=
  .snoc (.refl _) .walk_head

private theorem busyWitness :
    built = .done original heap ∧ Available heap original ∧
    walk 1 0 0 0 0 0 0 0 0 0 0 inherited 0 [original] running = .failed (.nodeMemo 0 .busy) busyAfter ∧
    busyAfter.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    busyRequest.key = request.key ∧
    SourceEqualityConstraintMemoAllocation.Grows running.checked.operations busyAfter.checked.operations ∧
    SourceEqualityConstraintAllocation.Ready busyAfter.checked.operations.constraints inherited ∧
    SourceEqualityConstraintFieldLookup.load plain busyAfter.checked.operations.constraints = .ok (some ⟨inherited,.top⟩) := by
  have builtDone : built = .done original heap := by cbv
  have verified := InternedFreshOrdinaryFacts.closed_verified program
  have initialReady : SourceEqualityConstraintAllocation.Ready running.checked.operations.constraints inherited :=
    (SourceCurrentAllocatedPartialInitialization.operations_correct Cache.emptyState Cache.empty_valid).2.2
  have loaded : SourceEqualityConstraintFieldLookup.load plain running.checked.operations.constraints = .ok (some ⟨inherited,.top⟩) := by cbv
  exact ⟨builtDone,verified.result _ _ builtDone,busyDone,by cbv,by cbv,
    SourceCurrentOuterExecutionGrowth.reached busyPrefix,
    SourceCurrentOuterExecutionGrowth.ready busyPrefix inherited initialReady,
    SourceCurrentOuterExecutionGrowth.field busyPrefix plain ⟨inherited,.top⟩ loaded⟩

/-- An actual busy walk retains its active owner's full key, ready value, and literal loaded guard. -/
theorem busy_preserves :
    built = .done original heap ∧ Available heap original ∧
    walk 1 0 0 0 0 0 0 0 0 0 0 inherited 0 [original] running = .failed (.nodeMemo 0 .busy) busyAfter ∧
    busyAfter.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    busyRequest.key = request.key ∧
    SourceEqualityConstraintMemoAllocation.Grows running.checked.operations busyAfter.checked.operations ∧
    SourceEqualityConstraintAllocation.Ready busyAfter.checked.operations.constraints inherited ∧
    SourceEqualityConstraintFieldLookup.load plain busyAfter.checked.operations.constraints = .ok (some ⟨inherited,.top⟩) := busyWitness

private def nonemptyGuard : Guard := ⟨some [[[0,0],[0,1]]],.top⟩
private def nonemptyAllocation := SourceEqualityConstraintAllocation.construct nonemptyGuard.equalities Cache.emptyState
private def own : SourceEqualityConstraintAllocation.Value := match nonemptyAllocation.1 with | .ok value => value | _ => .contradiction
private def nonemptyBefore := SourceCurrentAllocatedPartialInitialization.caller 4 nonemptyAllocation.2 heap
private def childPair := SourceCurrentAllocatedPartialGraph.descend nonemptyBefore own 0
private def emptyRequest : NodeRequest := ⟨childPair.1,.empty⟩
private def emptyRunning := (beginNode emptyRequest childPair.2).2.2
private def emptyAfter := finishNode 0 .empty emptyRunning
private def nonemptyStart : Phase 4 := .walk 1 own 0 [.empty] nonemptyBefore
private def nonemptyEnd : Phase 4 := .walk 0 own 1 [] emptyAfter
private theorem ownCached : SourceEqualityGuardReadback.Cached nonemptyGuard.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0,0],[0,1]]] = .normalized [[[0,0],[0,1]]] := by cbv
  intro paths same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem emptyDone : nodeCall 0 0 0 0 0 0 0 0 0 0 0 emptyRequest childPair.2 = .done .empty emptyAfter := by cbv
private theorem nonemptyPrefix : Reached 0 0 0 0 0 0 0 0 0 0 nonemptyStart nonemptyEnd :=
  .snoc (.refl _) (.walk_tail emptyDone)

private theorem allocatingWitness :
    built = .done original heap ∧ Available heap original ∧
    walk 1 0 0 0 0 0 0 0 0 0 0 own 0 [.empty] nonemptyBefore = .done [.empty] emptyAfter ∧
    nonemptyBefore.checked.operations.constraints.next < emptyAfter.checked.operations.constraints.next ∧
    SourceEqualityConstraintMemoAllocation.Grows nonemptyBefore.checked.operations emptyAfter.checked.operations ∧
    SourceEqualityConstraintAllocation.Ready emptyAfter.checked.operations.constraints own ∧
    SourceEqualityConstraintFieldLookup.load nonemptyGuard emptyAfter.checked.operations.constraints = .ok (some ⟨own,.top⟩) ∧
    Cache.Valid emptyAfter.checked.operations.constraints := by
  have created := SourceEqualityConstraintFieldLookup.load_of_construct nonemptyGuard ownCached Cache.emptyState Cache.empty_valid
    own nonemptyAllocation.2 (show nonemptyAllocation = (.ok own,nonemptyAllocation.2) by cbv)
  have valid := created.2.2.2.2
  have allocation := SourceCurrentAllocatedPartialInitialization.operations_correct nonemptyAllocation.2 valid
  have initialReady := created.2.2.1.grows allocation.2.1.constraint_growth
  have initialLoad := SourceCurrentConjunctionEquality.load_grows nonemptyGuard _ _ allocation.2.1 ⟨own,.top⟩ created.1
  have builtDone : built = .done original heap := by cbv
  refine ⟨builtDone,(InternedFreshOrdinaryFacts.closed_verified program).result _ _ builtDone,?_,by cbv,
    SourceCurrentOuterExecutionGrowth.reached nonemptyPrefix,
    SourceCurrentOuterExecutionGrowth.ready nonemptyPrefix own initialReady,
    SourceCurrentOuterExecutionGrowth.field nonemptyPrefix nonemptyGuard ⟨own,.top⟩ initialLoad,
    SourceCurrentOuterExecutionGrowth.cache_valid nonemptyPrefix allocation.1.constraints⟩
  simp only [walk,emptyDone,Outcome.bind]

/-- A completed indexed walk allocates a new constraint while retaining the complete original field. -/
theorem allocating_walk :
    built = .done original heap ∧ Available heap original ∧
    walk 1 0 0 0 0 0 0 0 0 0 0 own 0 [.empty] nonemptyBefore = .done [.empty] emptyAfter ∧
    nonemptyBefore.checked.operations.constraints.next < emptyAfter.checked.operations.constraints.next ∧
    SourceEqualityConstraintMemoAllocation.Grows nonemptyBefore.checked.operations emptyAfter.checked.operations ∧
    SourceEqualityConstraintAllocation.Ready emptyAfter.checked.operations.constraints own ∧
    SourceEqualityConstraintFieldLookup.load nonemptyGuard emptyAfter.checked.operations.constraints = .ok (some ⟨own,.top⟩) ∧
    Cache.Valid emptyAfter.checked.operations.constraints := allocatingWitness

end MicroCFTA.ActiveGrowthKernels

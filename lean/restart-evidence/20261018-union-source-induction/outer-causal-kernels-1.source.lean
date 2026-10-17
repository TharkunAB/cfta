import MicroCFTA.SourceCurrentOuterActiveAncestry
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
set_option linter.all true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option cbv.maxSteps 1000000
namespace OuterCausalKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterActiveAncestry
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
private theorem edgeGraph : SourceCurrentAllocatedPartialGraph.EdgeCall 0 edgeRequest running sentinel parentReturn := by
  apply SourceCurrentAllocatedPartialGraph.EdgeCall.evaluate edgeStarted
  apply SourceCurrentAllocatedPartialGraph.EdgeBody.parent (loaded := ⟨inherited,.top⟩)
  · intro impossible
    rw [rejected] at impossible
    cases impossible
  · exact SourceCurrentAllocatedParentEdge.Edge.rejected rejected
private theorem edgeDone : edgeCall 3 0 0 0 0 0 0 0 0 0 0 edgeRequest running = .done sentinel parentReturn := by
  simp only [edgeCall,edgeStarted,edgeBody,SourceCurrentAllocatedParentWorker.edge,rejected,ite_true,
    Outcome.bind,parentReturn,sentinel]
  rfl
private theorem prefixDone :
    (SourceCurrentAllocatedInheritedPrefix.run sentinel.entry.key.constraint inherited parentReturn.checked.operations).1 =
      .ok (some combined) := by cbv
private theorem reached : Reached 0 0 0 0 0 0 0 0 0 0 start inChild := by
  have first : Reached 0 0 0 0 0 0 0 0 0 0 start (.body 5 request running) :=
    .snoc (.refl _) (.node_evaluate rootStarted)
  have rows : Reached 0 0 0 0 0 0 0 0 0 0 start (.rows 4 inherited [sourceRow] running) :=
    .snoc first (.body_rows (by cbv))
  have edge : Reached 0 0 0 0 0 0 0 0 0 0 start (.descendants 3 inherited sentinel parentReturn) :=
    .snoc rows (.rows_edge edgeDone edgeGraph)
  have children : Reached 0 0 0 0 0 0 0 0 0 0 start (.children 3 combined [.empty] prefixed) := by
    exact .snoc edge (.descendants_children prefixDone)
  have walked : Reached 0 0 0 0 0 0 0 0 0 0 start (.walk 3 combined 0 [.empty] prefixed) :=
    .snoc children (.children_walk (by cbv))
  have demanded : Reached 0 0 0 0 0 0 0 0 0 0 start atChild := .snoc walked .walk_head
  exact .snoc demanded (.node_evaluate childStarted)
private theorem childGraph : SourceCurrentAllocatedPartialGraph.NodeCall 0 child descended.2 .empty childAfter :=
  .evaluate childStarted .empty
private theorem childDone : nodeCall 2 0 0 0 0 0 0 0 0 0 0 child descended.2 = .done .empty childAfter := by
  simp only [nodeCall,childStarted,nodeBody,child,Outcome.bind,childAfter]
private theorem returned : Reached 0 0 0 0 0 0 0 0 0 0 start afterChild := by
  have first : Reached 0 0 0 0 0 0 0 0 0 0 start (.body 5 request running) :=
    .snoc (.refl _) (.node_evaluate rootStarted)
  have rows : Reached 0 0 0 0 0 0 0 0 0 0 start (.rows 4 inherited [sourceRow] running) :=
    .snoc first (.body_rows (by cbv))
  have edge : Reached 0 0 0 0 0 0 0 0 0 0 start (.descendants 3 inherited sentinel parentReturn) :=
    .snoc rows (.rows_edge edgeDone edgeGraph)
  have children : Reached 0 0 0 0 0 0 0 0 0 0 start (.children 3 combined [.empty] prefixed) :=
    .snoc edge (.descendants_children prefixDone)
  have walked : Reached 0 0 0 0 0 0 0 0 0 0 start (.walk 3 combined 0 [.empty] prefixed) :=
    .snoc children (.children_walk (by cbv))
  exact .snoc walked (.walk_tail childDone childGraph)
/-- An actual rejected parent reaches two protected node owners from a built source and empty tables. -/
theorem two_owners :
    built = .done original heap ∧ Available heap original ∧
    Reached 0 0 0 0 0 0 0 0 0 0 start inChild ∧
    childRunning.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    childRunning.nodeResults.cells 1 = some ⟨child,.evaluating⟩ ∧
    Ancestor 0 0 0 0 0 0 0 0 0 0 start inChild 0 request ∧
    Ancestor 0 0 0 0 0 0 0 0 0 0 start inChild 1 child ∧
    (∀ handle owner, childRunning.nodeResults.cells handle = some ⟨owner,.evaluating⟩ →
      Ancestor 0 0 0 0 0 0 0 0 0 0 start inChild handle owner) := by
  have actual : built = .done original heap := by cbv
  have facts := InternedFreshOrdinaryFacts.closed_verified program
  have available := facts.result original heap actual
  have rootCell : childRunning.nodeResults.cells 0 = some ⟨request,.evaluating⟩ := by cbv
  have childCell : childRunning.nodeResults.cells 1 = some ⟨child,.evaluating⟩ := by cbv
  have all := reached.owners (SourceCurrentAllocatedPartialFrames.initial_protocol _ _ _)
    (fun _ _ impossible => by cases impossible)
  exact ⟨actual,available,reached,rootCell,childCell,all 0 request rootCell,all 1 child childCell,all⟩
/-- The exact completed child prefix removes its owner while retaining its enclosing root activation. -/
theorem completed_suffix :
    Reached 0 0 0 0 0 0 0 0 0 0 start afterChild ∧
    childAfter.nodeResults.cells 0 = some ⟨request,.evaluating⟩ ∧
    childAfter.nodeResults.cells 1 = some ⟨child,.returned .empty⟩ ∧
    (∀ handle owner, childAfter.nodeResults.cells handle = some ⟨owner,.evaluating⟩ →
      Ancestor 0 0 0 0 0 0 0 0 0 0 start afterChild handle owner) := by
  have all := returned.owners (SourceCurrentAllocatedPartialFrames.initial_protocol _ _ _)
    (fun _ _ impossible => by cases impossible)
  exact ⟨returned,by cbv,by cbv,all⟩
end OuterCausalKernels
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @OuterCausalKernels.two_owners
#print OuterCausalKernels.two_owners
#print axioms OuterCausalKernels.two_owners
#check @OuterCausalKernels.completed_suffix
#print OuterCausalKernels.completed_suffix
#print axioms OuterCausalKernels.completed_suffix

import MicroCFTA.SourceCurrentHeadMuGeneration

/-!
# A Head unfold installs a new nested Mu

The original outer Mu contains an inner Mu that captures outer self.
Unfolding rebuilds that inner binder with the complete outer Mu. The exact
new full cell is selected at the Head return. One application of the Head
producer derives its same operation and generated rooted writer.
-/
namespace MicroCFTA.HeadMuGenerationFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open InternedStoredSubstitution (leaves input encode)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredHead (Head)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentCompletedBuildRootedWriters (Written)
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool
local notation "Row" => EdgeValue Nat Bool
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.binder false (.node [.mk 8 false [.var 1,.var 0]])]])
private def valueOf (outcome : Outcome Nat Bool Node) : Node :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def sourceCall := build expression [] (empty : Heap)
private def parent : Node := valueOf sourceCall
private def before : Heap := sourceCall.state
private def unfolded := unfold parent before
private def output : Node := valueOf unfolded
private def unfoldedAfter : Heap := unfolded.state
private def row : Row := (nodeEdges output)[0]?.getD
  (run (makeEdge 0 false []) before).1
private def child : Node := row.children[0]?.getD .empty
private def childEntry := match child with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def childBody : Node := match child with | .mu _ body _ _ => body | _ => .empty
private def childDepth : Node := match child with | .mu _ _ depth _ => depth | _ => .empty
private def childOrdinary : Node := match child with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def headCall := run (makeNode (nodeEdges output)) unfoldedAfter
private def headValue : Node := headCall.1
private def after : Heap := headCall.2

private theorem built : build expression [] (empty : Heap) = .done parent before := by cbv
private theorem unfolded_done : unfold parent before = .done output unfoldedAfter := by cbv
private theorem child_shape : child = .mu childEntry childBody childDepth childOrdinary := by cbv
private theorem missing : before.nodeRecords childEntry.key = none := by cbv
private theorem present : after.nodeRecords childEntry.key = some child := by cbv
private theorem child_selected : (nodeEdges output)[0]? = some row ∧ row.children[0]? = some child := by cbv
private theorem actual_head : Head parent before headValue after := by
  refine .read 0 (nodeEdges output) unfoldedAfter ?_ rfl
  cbv
private theorem warm_head : Head parent after headValue after := by
  refine .read 0 (nodeEdges output) after ?_ ?_
  · cbv
  · cbv
private theorem semantic : SemanticReady before :=
  SourceEqualityRequiredSemanticCache.constructed expression parent before built
private theorem costs : CostHeap before :=
  InternedFreshOrdinaryCosts.closed_heap expression
private theorem available : Available before parent :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result parent before built

private theorem checked_witness :
    build expression [] (empty : Heap) = .done parent before ∧
    SemanticReady before ∧ CostHeap before ∧ Available before parent ∧
    unfold parent before = .done output unfoldedAfter ∧
    (nodeEdges output)[0]? = some row ∧ row.children[0]? = some child ∧
    child = .mu childEntry childBody childDepth childOrdinary ∧
    before.nodeRecords childEntry.key = none ∧ after.nodeRecords childEntry.key = some child ∧
    Head parent before headValue after ∧ Head parent after headValue after ∧
  ∃ parentEntry parentBody parentDepth parentOrdinary operationBefore operationResult operationAfter,
    SemanticReady operationBefore ∧ CostHeap operationBefore ∧
    Available operationBefore (.mu parentEntry parentBody parentDepth parentOrdinary) ∧
    unfold (.mu parentEntry parentBody parentDepth parentOrdinary)
      operationBefore = .done operationResult operationAfter ∧
    operationBefore.nodeRecords childEntry.key = none ∧
    operationAfter.nodeRecords childEntry.key = some child ∧
    Nonempty (Path before operationBefore) ∧ Grows operationAfter after ∧
    Extends operationAfter.nodes.issued after.nodes.issued ∧
    Context operationBefore ((leaves parentBody).map (input (fun name =>
      if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none))) ∧
    build (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input (fun name =>
        if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
      operationBefore = .done operationResult operationAfter ∧
    Written (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input (fun name =>
        if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
      operationBefore operationAfter childEntry.key child := by
  have selected : after.nodeRecords childEntry.key = some (.mu childEntry childBody childDepth childOrdinary) := by
    rw [←child_shape]
    exact present
  have generated := SourceCurrentHeadMuGeneration.head actual_head semantic costs available
    childEntry.key childEntry childBody childDepth childOrdinary selected
  rcases generated with prior | generated
  · rw [missing] at prior
    cases prior
  · refine ⟨built,semantic,costs,available,unfolded_done,child_selected.1,child_selected.2,
      child_shape,missing,present,actual_head,warm_head,?_⟩
    simpa only [←child_shape] using generated

/-- Actual cold Head generation derives the selected new nested Mu writer and a later warm Head. -/
theorem actual_nested_generation :
    build expression [] (empty : Heap) = .done parent before ∧
    SemanticReady before ∧ CostHeap before ∧ Available before parent ∧
    unfold parent before = .done output unfoldedAfter ∧
    (nodeEdges output)[0]? = some row ∧ row.children[0]? = some child ∧
    child = .mu childEntry childBody childDepth childOrdinary ∧
    before.nodeRecords childEntry.key = none ∧ after.nodeRecords childEntry.key = some child ∧
    Head parent before headValue after ∧ Head parent after headValue after ∧
  ∃ parentEntry parentBody parentDepth parentOrdinary operationBefore operationResult operationAfter,
    SemanticReady operationBefore ∧ CostHeap operationBefore ∧
    Available operationBefore (.mu parentEntry parentBody parentDepth parentOrdinary) ∧
    unfold (.mu parentEntry parentBody parentDepth parentOrdinary)
      operationBefore = .done operationResult operationAfter ∧
    operationBefore.nodeRecords childEntry.key = none ∧
    operationAfter.nodeRecords childEntry.key = some child ∧
    Nonempty (Path before operationBefore) ∧ Grows operationAfter after ∧
    Extends operationAfter.nodes.issued after.nodes.issued ∧
    Context operationBefore ((leaves parentBody).map (input (fun name =>
      if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none))) ∧
    build (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input (fun name =>
        if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
      operationBefore = .done operationResult operationAfter ∧
    Written (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input (fun name =>
        if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
      operationBefore operationAfter childEntry.key child := checked_witness

end MicroCFTA.HeadMuGenerationFixture

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.HeadMuGenerationFixture.actual_nested_generation
#print MicroCFTA.HeadMuGenerationFixture.actual_nested_generation
#print axioms MicroCFTA.HeadMuGenerationFixture.actual_nested_generation

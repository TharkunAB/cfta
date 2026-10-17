import MicroCFTA.SourceCurrentOuterCopiedWarmHit
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

namespace MicroCFTA.CopiedWarmIntegration
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentOuterCopiedWarmHit
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance


/-- The reached internal hit skips every lower worker bound while enclosing owners remain active. -/
theorem reached_hit_all_fuels :
    ∃ (program : InternedNestedConstruction.Syntax Symbol Guard) (input b : Node) (initial hit : Caller 8)
      (owner first copied wrapperOwner : NodeRequest),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input initial.checked.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready initial.checked ∧
      Reached 16 16 16 16 16 16 16 16 128 0 (.node 24 owner initial) (.node 17 copied hit) ∧
      first.inherited = copied.inherited ∧ copied.value = b ∧
      hit.nodeResults.cells 1 = some ⟨first, .returned b⟩ ∧
      hit.nodeResults.cells 0 = some ⟨owner, .evaluating⟩ ∧
      hit.nodeResults.cells 3 = some ⟨wrapperOwner, .evaluating⟩ ∧
      ∀ fuel g s r e p h m c n budget,
        SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget copied hit = .done b hit := by
  obtain ⟨program, input, b, initial, owner, first, copied, wrapperOwner, firstBefore, firstAfter, hit,
    built, ready, available, closed, nodesEmpty, edgesEmpty, ownerEq, firstEq, copiedEq, keyEq,
    inheritedEq, guard, firstReach, firstDone, hitReach, published, returned, rootActive,
    wrapperActive, demand, done⟩ := copied_ready_while_owners_active
  refine ⟨program, input, b, initial, hit, owner, first, copied, wrapperOwner, built, ready,
    hitReach, inheritedEq, copiedEq, returned, rootActive, wrapperActive, ?_⟩
  intro fuel g s r e p h m c n budget
  exact SourceCurrentAllocatedPartialWorker.nodeCall_ready fuel g s r e p h m c n budget
    copied hit hit 1 b demand

private def plain : Guard := ⟨some [], .top⟩
private def program : InternedNestedConstruction.Syntax Symbol Guard := .node [.mk ("leaf", .top) plain []]
private def built := InternedFreshOrdinaryConstruction.build program [] empty
private def value : Node := match built with | .done result _ => result | .pending .. => .empty
private def initial := SourceCurrentAllocatedPartialInitialization.caller 8 Cache.emptyState built.state
private def request : NodeRequest := ⟨.contradiction, value⟩
private def running := (beginNode request initial).2.2

/-- Literal zero-fuel ordinary failure propagates through the evaluating owner's protected finish. -/
theorem concrete_failure_transport :
    SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request initial =
      .failed (.exhausted .nodeBody) running ∧
    running.nodeResults.cells 0 = some ⟨request, .evaluating⟩ := by
  have entered : beginNode request initial = (0, .evaluate request, running) := by cbv
  have reached : Reached 0 0 0 0 0 0 0 0 0 0 (.node 0 request initial) (.body 0 request running) :=
    .step (.node_evaluate entered) .refl
  have failed : (Phase.body 0 request running).run 0 0 0 0 0 0 0 0 0 0 =
      .failed (.exhausted .nodeBody) running := by cbv
  have result := reached.failed failed
  constructor
  · change (SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request initial).bind
      (fun _ after => .done () after) = .failed (.exhausted .nodeBody) running at result
    cases same : SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request initial with
    | done output after => simp only [same, SourceCurrentAllocatedPartialWorker.Outcome.bind] at result; cases result
    | failed fault after =>
        simp only [same, SourceCurrentAllocatedPartialWorker.Outcome.bind] at result
        exact result
  · cbv

end MicroCFTA.CopiedWarmIntegration
#check @MicroCFTA.CopiedWarmIntegration.reached_hit_all_fuels
#print axioms MicroCFTA.CopiedWarmIntegration.reached_hit_all_fuels
#check @MicroCFTA.CopiedWarmIntegration.concrete_failure_transport
#print axioms MicroCFTA.CopiedWarmIntegration.concrete_failure_transport

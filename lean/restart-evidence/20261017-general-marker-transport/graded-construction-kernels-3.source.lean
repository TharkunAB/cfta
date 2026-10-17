import MicroCFTA.SourceCurrentConstrainedCapConstruction
import MicroCFTA.InternedRecordDepthCompletion
import MicroCFTA.InternedFreshOrdinaryCoverage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.GradedConstructionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentConstrainedCapConstruction

/-- The first actual source capture has a guard outside the hereditary predicate. -/
def capturePlan : Syntax Nat Bool := .node [.mk 0 false []]

/-- Two nested literal binders use only their fresh local references. -/
def nestedPlan : Syntax Nat Bool :=
  .node [.mk 10 false [.binder false (.node [.mk 11 true [.var 0,
    .binder false (.node [.mk 12 true [.var 0, .var 1]])]])]]

private def badRoot : Value Nat Bool → Bool
  | .node _ (edge :: _) _ _ => !edge.entry.key.constraint
  | _ => false

private theorem annotated_not_bad (value : Value Nat Bool) (annotated : Annotated (fun guard => guard = true) value) :
    badRoot value = false := by
  cases annotated with
  | empty | reference | union | mu => rfl
  | node entry edges depth free guards children =>
      cases edges with
      | nil => rfl
      | cons edge rest =>
          have allowed := guards edge List.mem_cons_self
          simp only [badRoot, allowed, Bool.not_true]

/-- Mixed captures do not constrain binder subplans that use only their fresh lexical references. -/
theorem nested_typed (environment : List (Value Nat Bool)) :
    Typed (fun guard => guard = true) 1 nestedPlan environment := by
  have reference (name : InternedBinderProtocol.Reference) :
      Cap (fun guard : Bool => guard = true) 0 (.reference name : Value Nat Bool) := .plain 0 (.reference name)
  simp [nestedPlan, Typed, ManyTyped, EdgesTyped, reference]

/-- An initial cap capture feeds a second finite nested reconstruction without a hereditary heap premise. -/
theorem initial_mixed_nested :
    ∃ capture initial result after,
      InternedFreshOrdinaryConstruction.build capturePlan [] empty = .done capture initial ∧
      Cap (fun guard : Bool => guard = true) 1 capture ∧ ¬Annotated (fun guard => guard = true) capture ∧
      InternedFreshOrdinaryConstruction.build nestedPlan [capture] initial = .done result after ∧
      Cap (fun guard : Bool => guard = true) 1 result ∧ MuStored (fun guard => guard = true) after := by
  obtain ⟨capture, initial, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete capturePlan
  have typed : Typed (fun guard => guard = true) 1 capturePlan [] := by
    simp [capturePlan, Typed, EdgesTyped, ManyTyped]
  have constructed := build (fun guard => guard = true) 1 capturePlan [] empty empty_facts
    (by intro value member; cases member) typed (MuStored.empty _)
  have captureBound := constructed.result capture initial done
  have captureStored : MuStored (fun guard => guard = true) initial := by
    simpa only [done, Outcome.state] using constructed.stored
  have actualBad : (match InternedFreshOrdinaryConstruction.build capturePlan [] empty with
      | .done value _ => badRoot value
      | .pending _ _ => false) = true := by
    simp only [capturePlan, InternedFreshOrdinaryConstruction.build,
      InternedFreshOrdinaryConstruction.buildMany, InternedFreshOrdinaryConstruction.buildEdges,
      Outcome.bind, InternedNestedConstruction.work]
    simp [badRoot, makeNode, makeEdge, canonicalEdges, surviving, run, edgeStep, nodeStep,
      empty, Cache.intern, Cache.emptyState, Cache.keepFirst, Cache.put, identifyNode,
      EnumerationBuilderCaches.canonicalIds]
  rw [done] at actualBad
  have notAnnotated : ¬Annotated (fun guard => guard = true) capture := by
    intro annotated
    have impossible := annotated_not_bad capture annotated
    simp only [actualBad, Bool.true_eq_false] at impossible
  have physical := InternedFreshOrdinaryFacts.closed_verified capturePlan
  have facts : Facts initial := by simpa only [done, Outcome.state] using physical.facts
  have available := physical.result capture initial done
  have sourceContext := InternedFreshOrdinaryContext.empty_context.build capturePlan
  have context : InternedFreshOrdinaryContext.Context initial [] := by
    simpa only [done, Outcome.state] using sourceContext
  have inputs : InternedNestedProvenance.Values initial [capture] := by
    intro value member
    exact (List.mem_singleton.mp member) ▸ available
  have mixed : InternedFreshOrdinaryContext.Context initial [capture] :=
    ⟨context.normal, inputs, context.profiles, context.freeNames⟩
  have depth := InternedRecordDepthExecution.build_depth capturePlan [] empty
    InternedFreshOrdinaryContext.empty_context InternedFreshOrdinaryDepthHeap.empty_heap
  have heap : InternedFreshOrdinaryDepthHeap.Heap initial := by simpa only [done, Outcome.state] using depth.heap
  have covered : Covered [] initial := InternedFreshOrdinaryCoverage.build_covered capturePlan [] empty
    empty_facts.coherent.valid empty_correct.2 capture initial done
  obtain ⟨result, after, completed⟩ := InternedRecordDepthCompletion.source_complete nestedPlan [capture] initial mixed heap covered
  have rebuilt := build (fun guard => guard = true) 1 nestedPlan [capture] initial facts inputs
    (nested_typed [capture]) captureStored
  refine ⟨capture, initial, result, after, done, captureBound, notAnnotated, completed,
    rebuilt.result result after completed, ?_⟩
  simpa only [completed, Outcome.state] using rebuilt.stored

#print axioms nested_typed
#check @nested_typed
#print axioms initial_mixed_nested
#check @initial_mixed_nested
end MicroCFTA.GradedConstructionKernels

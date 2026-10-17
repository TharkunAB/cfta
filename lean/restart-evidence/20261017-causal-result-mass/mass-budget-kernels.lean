import MicroCFTA.SourceCurrentAllocatedRecursiveMassBudget
import MicroCFTA.SourceRecursiveIntersectionMaybeMuCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.MassBudgetIndependentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedValueMassHeap (Stored initialBound)
open SourceCurrentAllocatedRecursiveMassBudget (ceiling charge)
variable {Symbol Guard : Type}

/-- A fresh source construction and its own completed optional call share the initial numeric store and supply bounds. -/
theorem constructed_numeric_optional [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (pair : Nat × Nat) :
    ∃ body value before after,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection pair.1 pair.2)] empty = .done body before ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body before = .done value after ∧
      Available before body ∧ Available after value ∧
      Stored (initialBound before) before ∧ Stored (ceiling (initialBound before)) after ∧
      InternedValueMass.value body ≤ initialBound before ∧
      InternedValueMass.value value ≤ ceiling (initialBound before) ∧
      after.nodes.next ≤ before.nodes.next + charge (initialBound before) ∧
      after.edges.next ≤ before.edges.next + charge (initialBound before) := by
  have localAvailable : Available (empty : State Symbol Guard) (.reference (.intersection pair.1 pair.2)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection pair.1 pair.2 := List.mem_singleton.mp member
      cases impossible)
  have context := InternedFreshOrdinaryContext.empty_context.local (.intersection pair.1 pair.2) localAvailable
  obtain ⟨body, before, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete expression
    [.intersection pair.1 pair.2] empty context InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2
  change InternedFreshOrdinaryConstruction.build expression [.reference (.intersection pair.1 pair.2)] empty = .done body before at built
  have physical := InternedFreshOrdinaryFacts.build_verified expression _ empty empty_facts context.inputs
  have available := physical.result body before built
  have sourceContext : InternedFreshOrdinaryContext.Context before [.reference (.intersection pair.1 pair.2)] := by
    simpa only [built, Outcome.state] using context.build expression
  have sourceDepth : InternedFreshOrdinaryDepthHeap.Heap before := by
    simpa only [built, Outcome.state] using
      (InternedRecordDepthExecution.build_depth expression _ empty context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  have covered := InternedFreshOrdinaryCoverage.build_covered expression _ empty empty_valid InternedRecordCoherence.empty_correct.2 body before built
  obtain ⟨value, after, done, _afterContext, _afterDepth, _afterCovered, output, _growth, _history⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete_decoded pair body before sourceContext available sourceDepth covered
  have initialStored := InternedValueMassHeap.initial before sourceContext.normal.facts
  have resource := SourceCurrentAllocatedRecursiveMassBudget.initial pair body before sourceContext.normal.facts available
  have afterStored : Stored (ceiling (initialBound before)) after := by
    simpa only [done, Outcome.state] using resource.1
  have nodeBound : after.nodes.next ≤ before.nodes.next + charge (initialBound before) := by
    simpa only [done, Outcome.state] using resource.2.1
  have edgeBound : after.edges.next ≤ before.edges.next + charge (initialBound before) := by
    simpa only [done, Outcome.state] using resource.2.2.1
  exact ⟨body, value, before, after, built, done, available, output, initialStored, afterStored,
    InternedValueMassHeap.available before initialStored body available, resource.2.2.2 value after done, nodeBound, edgeBound⟩

/-- A genuinely open nested Mu uses the full source schedule and the same symbolic numeric ceiling. -/
theorem constructed_open_nested_numeric :
    ∃ (body value : Value Nat Bool) (before after : State Nat Bool),
      InternedFreshOrdinaryConstruction.build
        (.binder false (.node [.mk 0 true [.var 0, .var 1]])) [.reference (.intersection 3 5)] empty = .done body before ∧
      Reference.intersection 3 5 ∈ body.free ∧
      ¬InternedStoredClosedMuCompletion.PreparedWithoutMu body ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu (3, 5) body before = .done value after ∧
      Available before body ∧ Available after value ∧
      Stored (initialBound before) before ∧ Stored (ceiling (initialBound before)) after ∧
      InternedValueMass.value value ≤ ceiling (initialBound before) ∧
      after.nodes.next ≤ before.nodes.next + charge (initialBound before) ∧
      after.edges.next ≤ before.edges.next + charge (initialBound before) := by
  let expression : Syntax Nat Bool := .binder false (.node [.mk 0 true [.var 0, .var 1]])
  have observation : match InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty with
    | .pending .. => False
    | .done body _ => Reference.intersection 3 5 ∈ body.free ∧ (match body with | .mu .. => True | _ => False) := by
      set_option cbv.maxSteps 200000000 in
      cbv
      simp
      exact .head _
  obtain ⟨body, value, before, after, built, done, available, output, initialStored, finalStored, _bodyBound, resultBound, nodeBound, edgeBound⟩ :=
    constructed_numeric_optional expression (3, 5)
  rw [built] at observation
  dsimp only at observation
  have unsupported : ¬InternedStoredClosedMuCompletion.PreparedWithoutMu body := by
    intro prepared
    cases prepared with
    | closed body closed => rw [closed] at observation; cases observation.1
    | empty | reference | node | union => cases observation.2
  exact ⟨body, value, before, after, built, observation.1, unsupported, done,
    available, output, initialStored, finalStored, resultBound, nodeBound, edgeBound⟩

#print axioms constructed_numeric_optional
#check @constructed_numeric_optional
#print axioms constructed_open_nested_numeric
#check @constructed_open_nested_numeric
end MicroCFTA.MassBudgetIndependentKernels

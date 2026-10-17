import MicroCFTA.InternedFreshOrdinaryStoredAllocationBudget
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.StoredBudgetKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedFreshOrdinaryStoredAllocationBudget
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open InternedStoredShallowCompletion (BinderFree)

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0,
    .binder false (.node [.mk 1 true [.var 0, .var 1, .var 2]])]])

private theorem initial :
    ∃ input source, InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source ∧
      Available source input ∧
      InternedFreshOrdinaryContext.Context source [.reference (.intersection 3 5)] ∧
      InternedFreshOrdinaryDepthHeap.Heap source ∧ InternedRecordCoherence.Covered [] source := by
  have literal : Available (empty : State Nat Bool) (.reference (.intersection 3 5)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection 3 5 := List.mem_singleton.mp member
      cases impossible)
  have context := InternedFreshOrdinaryContext.empty_context.local (.intersection 3 5) literal
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete expression
    [.intersection 3 5] empty context InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2
  change InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source at built
  have checked := InternedFreshOrdinaryFacts.build_verified expression _ empty empty_facts context.inputs
  have contexts : InternedFreshOrdinaryContext.Context
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty).state
      [.reference (.intersection 3 5)] := context.build expression
  have depths : InternedFreshOrdinaryDepthHeap.Heap
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty).state :=
    (InternedRecordDepthExecution.build_depth expression _ empty context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  refine ⟨input, source, built, checked.result input source built,
    by simpa only [built, Outcome.state] using contexts,
    by simpa only [built, Outcome.state] using depths, ?_⟩
  exact InternedFreshOrdinaryCoverage.build_covered expression _ empty empty_valid InternedRecordCoherence.empty_correct.2 input source built

private theorem observed : match InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty with
    | .pending .. => False
    | .done input _ => Reference.intersection 3 5 ∈ input.free ∧
        ¬ BinderFree (encode (leaves input) [] input) ∧
        (match input with | .mu _ body _ _ => ¬ BinderFree (encode (leaves body) [] body) | _ => False) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 200000000 in cbv
  simp
  exact .head _

/-- Actual freshly built open nested Mu has all-outcome bounds for arbitrary replacement values and heaps. -/
theorem execute_arbitrary_replacements (replacement : Environment Nat Bool) (current : State Nat Bool) :
    ∃ input source,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source ∧
      Reference.intersection 3 5 ∈ input.free ∧ ¬ PreparedWithoutMu input ∧
      (execute input replacement current).state.nodes.next ≤ current.nodes.next + (executeCharges input).1 ∧
      (execute input replacement current).state.edges.next ≤ current.edges.next + (executeCharges input).2 := by
  obtain ⟨input, source, built, _available, _context, _depth, _covered⟩ := initial
  have shape := observed
  rw [built] at shape
  dsimp only at shape
  have noPreparation : ¬ PreparedWithoutMu input := by
    intro prepared
    exact shape.2.1 (InternedStoredClosedMuCompletion.encode_withoutMu (leaves input) [] input prepared)
  exact ⟨input, source, built, shape.1, noPreparation, execute_bound input replacement current⟩

/-- A fresh open nested Mu constructs its own successful unfolding with a non-binder-free stored body and exact-state bounds. -/
theorem constructed_unfold :
    ∃ input source result after,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source ∧
      Reference.intersection 3 5 ∈ input.free ∧
      (match input with | .mu _ body _ _ => ¬ PreparedWithoutMu body | _ => False) ∧
      unfold input source = .done result after ∧ Available after result ∧
      after.nodes.next ≤ source.nodes.next + (unfoldCharges input).1 ∧
      after.edges.next ≤ source.edges.next + (unfoldCharges input).2 := by
  obtain ⟨input, source, built, available, context, depth, covered⟩ := initial
  have shape := observed
  rw [built] at shape
  dsimp only at shape
  have nontrivial : match input with | .mu _ body _ _ => ¬ PreparedWithoutMu body | _ => False := by
    cases input with
    | mu entry body level ordinary =>
        intro prepared
        exact shape.2.2 (InternedStoredClosedMuCompletion.encode_withoutMu (leaves body) [] body prepared)
    | empty | reference | node | union => exact shape.2.2
  obtain ⟨result, after, done, _context, _depth, _covered, output, _growth, _history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded input source context available depth covered
  have counts := unfold_bound input source
  exact ⟨input, source, result, after, built, shape.1, nontrivial, done, output,
    by simpa only [done, Outcome.state] using counts⟩

end MicroCFTA.StoredBudgetKernels

#print axioms MicroCFTA.StoredBudgetKernels.execute_arbitrary_replacements
#check @MicroCFTA.StoredBudgetKernels.execute_arbitrary_replacements
#print axioms MicroCFTA.StoredBudgetKernels.constructed_unfold
#check @MicroCFTA.StoredBudgetKernels.constructed_unfold

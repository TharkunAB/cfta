import MicroCFTA.SourceCurrentAllocatedRecursiveOptionalBudget
import MicroCFTA.SourceRecursiveIntersectionMaybeMuCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.OptionalBudgetKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open IntersectionFlatMemoKeyDomain (Triple)
open SourceCurrentAllocatedRecursiveOptionalBudget
variable {Symbol Guard : Type}

/-- Arbitrary nested source with a literal pair capture constructs its own optional binder and counter bounds. -/
theorem constructed_optional [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (pair : Nat × Nat) :
    ∃ body value middle after,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection pair.1 pair.2)] empty = .done body middle ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body middle = .done value after ∧
      Available middle body ∧ Available after value ∧
      after.nodes.next ≤ middle.nodes.next + nodeBudget pair body ∧
      after.edges.next ≤ middle.edges.next + edgeBudget pair body := by
  have literal : Available (empty : State Symbol Guard) (.reference (.intersection pair.1 pair.2)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection pair.1 pair.2 := List.mem_singleton.mp member
      cases impossible)
  have context := InternedFreshOrdinaryContext.empty_context.local (.intersection pair.1 pair.2) literal
  obtain ⟨body, middle, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete expression
    [.intersection pair.1 pair.2] empty context InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2
  change InternedFreshOrdinaryConstruction.build expression [.reference (.intersection pair.1 pair.2)] empty = .done body middle at built
  have original := InternedFreshOrdinaryFacts.build_verified expression _ empty empty_facts context.inputs
  have available := original.result body middle built
  have nextContext : InternedFreshOrdinaryContext.Context
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection pair.1 pair.2)] empty).state
      [.reference (.intersection pair.1 pair.2)] := context.build expression
  have nextDepth : InternedFreshOrdinaryDepthHeap.Heap
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection pair.1 pair.2)] empty).state :=
    (InternedRecordDepthExecution.build_depth expression _ empty context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  have completedContext : InternedFreshOrdinaryContext.Context middle [.reference (.intersection pair.1 pair.2)] := by
    simpa only [built, Outcome.state] using nextContext
  have completedDepth : InternedFreshOrdinaryDepthHeap.Heap middle := by
    simpa only [built, Outcome.state] using nextDepth
  have covered := InternedFreshOrdinaryCoverage.build_covered expression _ empty empty_valid InternedRecordCoherence.empty_correct.2 body middle built
  obtain ⟨value, after, done, _context, _depth, _covered, output, _growth, _history⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete_decoded pair body middle completedContext available completedDepth covered
  have counters := bound pair body middle completedContext.normal.facts available
  exact ⟨body, value, middle, after, built, done, available, output,
    by simpa only [done, Outcome.state] using counters⟩

/-- The own successful optional binder yields an exact checked step with unchanged domains and memo tables. -/
theorem constructed_checked (width : Nat)
    (expression : Syntax (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (pair : Nat × Nat) (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (nodes : FlatMemoThunk.State (Triple width)
      (SourceRecursiveIntersectionThunks.NodeRequest (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))
      (Value (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula)))
    (edges : FlatMemoThunk.State (Triple width)
      (SourceRecursiveIntersectionThunks.EdgeRequest (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))
      (EdgeValue (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula)))
    (operations : SourceEqualityConstraintMemoAllocation.State)
    [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))] :
    ∃ body value middle after,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection pair.1 pair.2)] empty = .done body middle ∧
      SourceEqualityNativeDemand.step (.code (.optionalBinder pair body .pure))
          ⟨⟨⟨middle, domains⟩, nodes, edges⟩, operations⟩ =
        .yielded (.code (.pure value)) ⟨⟨⟨after, domains⟩, nodes, edges⟩, operations⟩ ∧
      after.nodes.next ≤ middle.nodes.next + nodeBudget pair body ∧
      after.edges.next ≤ middle.edges.next + edgeBudget pair body := by
  obtain ⟨body, value, middle, after, built, done, _available, _output, counts⟩ := constructed_optional expression pair
  exact ⟨body, value, middle, after, built, by
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, done,
      SourceEqualityNativeDemand.lift, SourceRecursiveIntersectionThunks.advance], counts⟩

/-- An actual open nested Mu defeats the old no-open-Mu preparation fragment and uses the full budget. -/
theorem used_nested_mu :
    ∃ (body value : Value Nat Bool) (middle after : State Nat Bool),
      InternedFreshOrdinaryConstruction.build
        (.binder false (.node [.mk 0 true [.var 0, .var 1]])) [.reference (.intersection 3 5)] empty = .done body middle ∧
      Reference.intersection 3 5 ∈ body.free ∧
      ¬ InternedStoredClosedMuCompletion.PreparedWithoutMu body ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu (3, 5) body middle = .done value after ∧
      nodeBudget (3, 5) body = 25 ∧ edgeBudget (3, 5) body = 9 ∧
      after.nodes.next ≤ middle.nodes.next + 25 ∧ after.edges.next ≤ middle.edges.next + 9 := by
  let expression : Syntax Nat Bool := .binder false (.node [.mk 0 true [.var 0, .var 1]])
  have observation : match InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty with
    | .pending .. => False
    | .done body _ => Reference.intersection 3 5 ∈ body.free ∧ nodeBudget (3, 5) body = 25 ∧
        edgeBudget (3, 5) body = 9 ∧ (match body with | .mu .. => True | _ => False) := by
      set_option maxRecDepth 30000 in
      set_option cbv.maxSteps 200000000 in cbv
      simp
      exact .head _
  obtain ⟨body, value, middle, after, built, done, _available, _output, counts⟩ := constructed_optional expression (3, 5)
  rw [built] at observation
  dsimp only at observation
  have noPrepared : ¬ InternedStoredClosedMuCompletion.PreparedWithoutMu body := by
    intro prepared
    cases prepared with
    | closed body closed => rw [closed] at observation; cases observation.1
    | empty | reference | node | union => cases observation.2.2.2
  exact ⟨body, value, middle, after, built, observation.1, noPrepared, done, observation.2.1, observation.2.2.1,
    by simpa only [observation.2.1, observation.2.2.1] using counts⟩

end MicroCFTA.OptionalBudgetKernels

#print axioms MicroCFTA.OptionalBudgetKernels.constructed_optional
#check @MicroCFTA.OptionalBudgetKernels.constructed_optional
#print axioms MicroCFTA.OptionalBudgetKernels.constructed_checked
#check @MicroCFTA.OptionalBudgetKernels.constructed_checked

#print axioms MicroCFTA.OptionalBudgetKernels.used_nested_mu
#check @MicroCFTA.OptionalBudgetKernels.used_nested_mu

import MicroCFTA.InternedFreshOrdinaryAllocationBudget
import MicroCFTA.SourceEqualityNativeDemand
import MicroCFTA.SourceRecursiveIntersectionMaybeMuCompletion

/-!
# Allocation bounds for the literal recursive optional binder

The current immutable body determines the complete encoded binder syntax.
The syntax bound includes both probes, any fresh body call, and nested Mu.
Unused pairs have zero effects. Used pairs retain the bound at every normal
or pending return. Checked instructions retain all native tables and operations.
This local bound is not an initial resource bound for a complete query.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveOptionalBudget
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Outcome Syntax)
open InternedBinderProtocol (Reference)
local notation "Fresh" => InternedFreshOrdinaryConstruction.build
local notation "maybeMu" => SourceRecursiveIntersectionMaybeMu.maybeMu
variable {Symbol Guard : Type}

/-- The full source callback plan retains every open nested binder. -/
def constructionSyntax (key : Nat × Nat) (body : Value Symbol Guard) : Syntax Symbol Guard :=
  .binder true (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves body)
    [.intersection key.1 key.2] body)

/-- Only a used pair can perform the complete encoded binder schedule. -/
def nodeBudget (key : Nat × Nat) (body : Value Symbol Guard) : Nat :=
  if Reference.intersection key.1 key.2 ∈ body.free then
    InternedFreshOrdinaryAllocationBudget.nodeBudget (constructionSyntax key body) else 0

/-- Edge allocation includes every repeated probe and fresh-body traversal. -/
def edgeBudget (key : Nat × Nat) (body : Value Symbol Guard) : Nat :=
  if Reference.intersection key.1 key.2 ∈ body.free then
    InternedFreshOrdinaryAllocationBudget.edgeBudget (constructionSyntax key body) else 0

/-- Initial body provenance derives both actual stopping-state supply bounds. -/
theorem bound [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state body) :
    (maybeMu key body state).state.nodes.next ≤ state.nodes.next + nodeBudget key body ∧
    (maybeMu key body state).state.edges.next ≤ state.edges.next + edgeBudget key body := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq key body state state facts available]
  by_cases used : Reference.intersection key.1 key.2 ∈ body.free
  · simp only [used, ite_true, nodeBudget, edgeBudget]
    exact InternedFreshOrdinaryAllocationBudget.build_bound (constructionSyntax key body)
      (InternedStoredSubstitution.leaves body) state
  · simp only [used, ite_false, nodeBudget, edgeBudget, Outcome.state, Nat.add_zero, Nat.le_refl, and_self]

/-- An absent pair returns the identical value and heap with both budgets zero. -/
theorem unused [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (absent : Reference.intersection key.1 key.2 ∉ body.free) :
    maybeMu key body state = .done body state ∧ nodeBudget key body = 0 ∧ edgeBudget key body = 0 := by
  exact ⟨SourceRecursiveIntersectionMaybeMu.unused key body state absent,
    by simp only [nodeBudget, absent, ite_false], by simp only [edgeBudget, absent, ite_false]⟩

section CheckedInstructions
local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Code" => SourceRecursiveIntersectionCode.Code
local notation "step" => SourceEqualityNativeDemand.step
local notation "Control" => SourceEqualityNativeDemand.Control
variable [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)] {width : Nat} {Output : Type}

/-- Every checked stopping outcome changes only the actual constructor heap. -/
theorem checked_state (key : Nat × Nat) (body : Value SourceSymbol SourceGuard)
    (next : Value SourceSymbol SourceGuard → Code SourceSymbol SourceGuard Output) (before : Checked width) :
    (step (.code (.optionalBinder key body next)) before).state =
      ⟨{before.native with machine := {before.native.machine with heap := (maybeMu key body before.native.machine.heap).state}},
        before.operations⟩ := by
  cases actual : maybeMu key body before.native.machine.heap <;>
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual,
      SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state,
      SourceRecursiveIntersectionThunks.advance, Outcome.state]

/-- A checked optional-binder instruction satisfies the same initial-body supply bounds. -/
theorem checked_bound (key : Nat × Nat) (body : Value SourceSymbol SourceGuard)
    (next : Value SourceSymbol SourceGuard → Code SourceSymbol SourceGuard Output) (before : Checked width)
    (facts : Facts before.native.machine.heap) (available : Available before.native.machine.heap body) :
    (step (.code (.optionalBinder key body next)) before).state.native.machine.heap.nodes.next ≤
      before.native.machine.heap.nodes.next + nodeBudget key body ∧
    (step (.code (.optionalBinder key body next)) before).state.native.machine.heap.edges.next ≤
      before.native.machine.heap.edges.next + edgeBudget key body := by
  rw [checked_state key body next before]
  exact bound key body before.native.machine.heap facts available

/-- A yielded checked instruction exposes its exact successful binder and unchanged side tables. -/
theorem checked_yielded (key : Nat × Nat) (body : Value SourceSymbol SourceGuard)
    (next : Value SourceSymbol SourceGuard → Code SourceSymbol SourceGuard Output)
    (before after : Checked width) (control : Control Output)
    (facts : Facts before.native.machine.heap) (available : Available before.native.machine.heap body)
    (yielded : step (.code (.optionalBinder key body next)) before = .yielded control after) :
    ∃ value heap, maybeMu key body before.native.machine.heap = .done value heap ∧
      control = .code (next value) ∧
      after = ⟨{before.native with machine := {before.native.machine with heap := heap}}, before.operations⟩ ∧
      heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget key body ∧
      heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget key body := by
  have counters := bound key body before.native.machine.heap facts available
  cases actual : maybeMu key body before.native.machine.heap with
  | done value heap =>
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual,
        SourceEqualityNativeDemand.lift] at yielded
      obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj yielded
      exact ⟨value, heap, rfl, rfl, rfl, by simpa only [actual, Outcome.state] using counters⟩
  | pending key heap =>
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual,
        SourceEqualityNativeDemand.lift] at yielded
      cases yielded

end CheckedInstructions
end MicroCFTA.SourceCurrentAllocatedRecursiveOptionalBudget

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
    reference_available empty _ (by intro identity member; simpa only [Value.free, List.mem_singleton, Reference.noConfusion] using member)
  have context := InternedFreshOrdinaryContext.empty_context.local (.intersection pair.1 pair.2) literal
  obtain ⟨body, middle, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete expression
    [.intersection pair.1 pair.2] empty context InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2
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

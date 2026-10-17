import MicroCFTA.InternedFreshOrdinaryAllocationBudget
import MicroCFTA.SourceEqualityNativeDemand

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

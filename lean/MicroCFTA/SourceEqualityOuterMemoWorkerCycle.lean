import MicroCFTA.SourceEqualityPartialMemoWorker
import MicroCFTA.SourceEqualityOuterCallerWorkerCycle

/-!
# The actual recursive memo worker reaches the running root thunk

The worker starts with empty constraint and result tables. It constructs the
original closed fixture and executes both native prefixes. The recursive
request reaches the published root thunk before either caller completes.
-/
namespace MicroCFTA.SourceEqualityOuterMemoWorkerCycle
open InternedConstructorTemplates InternedNestedConstruction
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph
open SourceEqualityPartialMemoWorker
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

attribute [local cbv_eval] array_small

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- The observation retains construction, the busy key, and the full final state. -/
structure Trace where
  root : Value Symbol Guard
  heap : InternedConstructorTemplates.State Symbol Guard
  key : Key
  handle : Nat
  state : SourceEqualityPartialMemoWorker.State 32

/-- Execute the recursive memo worker from the original cold source construction. -/
noncomputable def observation : Option Trace :=
  match InternedFreshOrdinaryConstruction.build SourceEqualityOuterCallerCycle.expression [] empty with
  | .pending .. => none
  | .done root heap =>
      match SourceEqualityPartialMemoWorker.run 4 4 2 2 2 1024 2 (some []) root
          (initial (SourceEqualityNativeInitial.cold 32 heap)) with
      | .incomplete (.busy key handle state) => some ⟨root, heap, key, handle, state⟩
      | _ => none

/-- Successful observation derives the full construction and recursive execution receipts. -/
theorem observation_receipts (observed : Trace) (found : observation = some observed) :
    InternedFreshOrdinaryConstruction.build SourceEqualityOuterCallerCycle.expression [] empty = .done observed.root observed.heap ∧
      SourceEqualityPartialMemoWorker.run 4 4 2 2 2 1024 2 (some []) observed.root
        (initial (SourceEqualityNativeInitial.cold 32 observed.heap)) = .incomplete (.busy observed.key observed.handle observed.state) := by
  unfold observation at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases found
  exact ⟨by assumption, by assumption⟩

/-- Check that two running cells include the original root and a distinct wrapper. -/
noncomputable def certificate : Bool :=
  match observation with
  | none => false
  | some observed =>
      match observed.state.memo.cells 0, observed.state.memo.cells 1 with
      | some ⟨root, .evaluating⟩, some ⟨wrapper, .evaluating⟩ =>
          decide (observed.key = (some 0, observed.root.referenceOf) ∧ observed.handle = 0 ∧
            observed.state.memo.next = 2 ∧ observed.state.memo.table observed.key = some 0 ∧
            root.value.referenceOf = observed.root.referenceOf ∧
            wrapper.value.referenceOf ≠ root.value.referenceOf) &&
          SourceEqualityPrecheck.isEmpty root.inherited && SourceEqualityPrecheck.isEmpty wrapper.inherited
      | _, _ => false

/-- Kernel execution observes the actual recursive request at the running root thunk. -/
theorem actual : certificate = true := by cbv

/-- The actual recursive receipt retains both running requests and their physical identities. -/
theorem actual_pending : ∃ observed root wrapper,
    observation = some observed ∧
    observed.state.memo.cells 0 = some ⟨root, .evaluating⟩ ∧
    observed.state.memo.cells 1 = some ⟨wrapper, .evaluating⟩ ∧
    observed.key = (some 0, observed.root.referenceOf) ∧ observed.handle = 0 ∧
    observed.state.memo.next = 2 ∧ observed.state.memo.table observed.key = some 0 ∧
    root.value.referenceOf = observed.root.referenceOf ∧
    wrapper.value.referenceOf ≠ root.value.referenceOf ∧
    SourceEqualityPrecheck.isEmpty root.inherited = true ∧ SourceEqualityPrecheck.isEmpty wrapper.inherited = true := by
  have checked := actual
  unfold certificate at checked
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨_, _, _, by assumption, by assumption, by assumption, ?_⟩
  exact ⟨checked.1.1.1, checked.1.1.2.1, checked.1.1.2.2.1, checked.1.1.2.2.2.1,
    checked.1.1.2.2.2.2.1, checked.1.1.2.2.2.2.2, checked.1.2, checked.2⟩

end MicroCFTA.SourceEqualityOuterMemoWorkerCycle

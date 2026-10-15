import MicroCFTA.SourceEqualityOuterCallerMemoCycle
import MicroCFTA.SourceEqualityPartialFirstDemand

/-!
# Actual outer worker requests in the closed caller cycle

A one-level worker stops at its first recursive child request.
The next worker uses that exact child and its returned warm state.
Both incomplete receipts retain their full source states. Neither
worker reaches modifyNode or a successful caller return.
-/
namespace MicroCFTA.SourceEqualityOuterCallerWorkerCycle
open InternedConstructorTemplates InternedNestedConstruction
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
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

open SourceEqualityPartialFirstDemand (waiting)

/-- Original construction and both actual outer worker requests retain their complete receipts. -/
structure Trace where
  root : Value Symbol Guard
  heap : State Symbol Guard
  wrapper : Value Symbol Guard
  middle : NativeState 32 Symbol Guard
  returned : Value Symbol Guard
  final : NativeState 32 Symbol Guard
  firstInherited : SourceEqualityPrecheck.Constraint
  secondInherited : SourceEqualityPrecheck.Constraint

/-- Execute the actual outer worker twice and retain the exact first incomplete callee each time. -/
noncomputable def observation : Option Trace :=
  match InternedFreshOrdinaryConstruction.build SourceEqualityOuterCallerCycle.expression [] empty with
  | .pending .. => none
  | .done root heap =>
      match SourceEqualityPartialWorker.run 4 4 2 2 2 1024 1 (some []) root (SourceEqualityNativeInitial.cold 32 heap) with
      | .incomplete (.rows (.incomplete (.children (.exhausted firstInherited wrapper middle)))) =>
          match SourceEqualityPartialWorker.run 4 4 2 2 2 1024 1 firstInherited wrapper middle with
          | .incomplete (.rows (.incomplete (.children (.exhausted secondInherited returned final)))) =>
              some ⟨root, heap, wrapper, middle, returned, final, firstInherited, secondInherited⟩
          | _ => none
      | _ => none

/-- The full original construction and both incomplete worker receipts use the actual returned states. -/
def Receipts (observed : Trace) : Prop :=
  InternedFreshOrdinaryConstruction.build SourceEqualityOuterCallerCycle.expression [] empty = .done observed.root observed.heap ∧
    SourceEqualityPartialWorker.run 4 4 2 2 2 1024 1 (some []) observed.root (SourceEqualityNativeInitial.cold 32 observed.heap) =
      waiting observed.firstInherited observed.wrapper observed.middle ∧
    SourceEqualityPartialWorker.run 4 4 2 2 2 1024 1 observed.firstInherited observed.wrapper observed.middle =
      waiting observed.secondInherited observed.returned observed.final

/-- Observing the actual worker supplies its full construction, callee, and warm-state equalities. -/
theorem observation_receipts (observed : Trace) (found : observation = some observed) : Receipts observed := by
  unfold observation at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases found
  exact ⟨by assumption, by assumption, by assumption⟩

/-- The verified fixture uses one ordinary row at each demanded caller. -/
def oneRow : Value Symbol Guard → Bool
  | .node _ [_] _ _ => true
  | _ => false

/-- A successful row test exposes the actual ordinary node and its sole edge. -/
theorem oneRow_shape (value : Value Symbol Guard) (checked : oneRow value = true) :
    ∃ entry edge depth free, value = .node entry [edge] depth free := by
  cases value with
  | empty => simp [oneRow] at checked
  | reference name => simp [oneRow] at checked
  | mu entry body depth ordinary => simp [oneRow] at checked
  | union entry members depth free => simp [oneRow] at checked
  | node entry edges depth free =>
      cases edges with
      | nil => simp [oneRow] at checked
      | cons edge edges =>
          cases edges with
          | nil => exact ⟨entry, edge, depth, free, rfl⟩
          | cons other rest => simp [oneRow] at checked

/-- A successful ordinary body must complete its specified first child at that exact warm state. -/
def Requires (inherited : SourceEqualityPrecheck.Constraint) (parent : Value Symbol Guard) (before : NativeState 32 Symbol Guard)
    (childInherited : SourceEqualityPrecheck.Constraint) (child : Value Symbol Guard) (reached : NativeState 32 Symbol Guard) : Prop :=
  ∀ (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState 32 Symbol Guard → SourceEqualityPartialWorker.Result 32)
    result after, SourceEqualityPartialWorker.step call 4 4 2 2 2 1024 inherited parent before = .done (.ok result) after →
      ∃ value middle, call childInherited child reached = .done (.ok value) middle

/-- Both actual one-row caller bodies require the next certified child before successful return. -/
theorem required (observed : Trace) (found : observation = some observed)
    (rootRow : oneRow observed.root = true) (wrapperRow : oneRow observed.wrapper = true) :
    Requires (some []) observed.root (SourceEqualityNativeInitial.cold 32 observed.heap)
        observed.firstInherited observed.wrapper observed.middle ∧
      Requires observed.firstInherited observed.wrapper observed.middle observed.secondInherited observed.returned observed.final := by
  have receipts := observation_receipts observed found
  obtain ⟨rootEntry, rootEdge, rootDepth, rootFree, rootShape⟩ := oneRow_shape _ rootRow
  obtain ⟨wrapperEntry, wrapperEdge, wrapperDepth, wrapperFree, wrapperShape⟩ := oneRow_shape _ wrapperRow
  constructor
  · intro call result after finished
    exact SourceEqualityPartialFirstDemand.first_required call 4 4 2 2 2 1024 _ _ rootEntry rootEdge rootDepth rootFree _ _ _
      (by simpa only [rootShape] using receipts.2.1) result after (by simpa only [rootShape] using finished)
  · intro call result after finished
    exact SourceEqualityPartialFirstDemand.first_required call 4 4 2 2 2 1024 _ _ wrapperEntry wrapperEdge wrapperDepth wrapperFree _ _ _
      (by simpa only [wrapperShape] using receipts.2.2) result after (by simpa only [wrapperShape] using finished)

/-- Check exact repeated node identity, empty inherited constructors, and distinct wrapper identity. -/
def closes (observed : Trace) : Bool :=
  decide (observed.returned.referenceOf = observed.root.referenceOf) &&
    SourceEqualityOuterCallerCycle.emptyPayload observed.firstInherited &&
    SourceEqualityOuterCallerCycle.emptyPayload observed.secondInherited &&
    decide (observed.wrapper.referenceOf ≠ observed.root.referenceOf) && oneRow observed.root && oneRow observed.wrapper

/-- Kernel evaluation follows both actual outer workers to their first incomplete child requests. -/
theorem actual_cycle : observation.map closes = some true := by cbv

/-- The actual outer worker receipts return to the identical empty-inherited physical root key. -/
theorem cycle : ∃ observed, observation = some observed ∧ observed.returned.referenceOf = observed.root.referenceOf ∧
    observed.firstInherited = some [] ∧ observed.secondInherited = some [] ∧
    observed.wrapper.referenceOf ≠ observed.root.referenceOf ∧ oneRow observed.root = true ∧ oneRow observed.wrapper = true := by
  cases found : observation with
  | none => have impossible := actual_cycle; simp [found] at impossible
  | some observed =>
      have checked : closes observed = true := by simpa only [found, Option.map_some, Option.some.injEq] using actual_cycle
      simp only [closes, Bool.and_eq_true, decide_eq_true_eq, SourceEqualityOuterCallerCycle.emptyPayload_iff] at checked
      rcases checked with ⟨⟨⟨⟨⟨same, first⟩, second⟩, different⟩, rootRow⟩, wrapperRow⟩
      exact ⟨observed, rfl, same, first, second, different, rootRow, wrapperRow⟩

/-- Actual outer worker requests instantiate the existing typed result-thunk busy trace. -/
theorem actual_pending : ∃ observed, observation = some observed ∧
    observed.firstInherited = some [] ∧ observed.secondInherited = some [] ∧
    observed.returned.referenceOf = observed.root.referenceOf ∧
    SourceEqualityOuterCallerMemoCycle.PendingCycle observed.root.referenceOf observed.wrapper.referenceOf ∧
    Receipts observed ∧
    Requires (some []) observed.root (SourceEqualityNativeInitial.cold 32 observed.heap)
        observed.firstInherited observed.wrapper observed.middle ∧
    Requires observed.firstInherited observed.wrapper observed.middle observed.secondInherited observed.returned observed.final := by
  obtain ⟨observed, found, same, first, second, different, rootRow, wrapperRow⟩ := cycle
  exact ⟨observed, found, first, second, same, SourceEqualityOuterCallerMemoCycle.pending _ _ different,
    observation_receipts observed found, required observed found rootRow wrapperRow⟩

end MicroCFTA.SourceEqualityOuterCallerWorkerCycle

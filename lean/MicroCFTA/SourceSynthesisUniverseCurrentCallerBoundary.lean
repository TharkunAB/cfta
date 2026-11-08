import MicroCFTA.SourceSynthesisUniverseCallerBoundary
import MicroCFTA.SourceCurrentAllocatedPartialWorker
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceEqualityOriginalAllocationPreparation

/-!
# An original request in the current allocated caller

The input is the same accepted one-component size-two source request.
The ordinary-symbol adapter retains its source names and Top refinements.
The original guard list passes through the actual serial field preparation.
Its returned cache initializes the current 64-bit allocated caller.

The current worker supplies every child request and inherited value.
Its separate node-result table retains the requested application and function.
The bounded return also retains the fourth memo and the exact diagnostic.
Merge fuel counts code, bind, and request layers. The first exposed universe
has five singleton groups. Its instruction calculation gives a bound of 22.
The observation uses 24 for this stage. This is not a bound for all targets.
The fourth memo remains empty in this prefix. This example does not attach
the tuple budget to a reached fourth decision. It does not prove native
scheduling, a busy-key recurrence, or a failure of termination.
-/
namespace MicroCFTA.SourceSynthesisUniverseCurrentCallerBoundary
open InternedConstructorTemplates InternedNestedConstruction
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceCurrentAllocatedPartialState (NodeRequest)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes =
      SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

private theorem eqGuard_small (classes : EqualityNormalize.Constraints) :
    SourceSynthesisGeneralizeSyntax.eqGuard classes =
      ⟨SymbolicEqualityBridge.resultClasses
        (SourceEqualityNormalizationReceipt.observed 16 classes), .top⟩ := by
  rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
  unfold SourceCompactGuards.normalize
  rw [array_small]

private theorem combine_small (first second : SourceEqualityPrecheck.Constraint) :
    SourceEqualityPrecheck.combine first second =
      match first, second with
      | none, _ | _, none => .contradiction
      | some [], some [] => .normalized []
      | some left, some right =>
          SourceEqualityNormalizationReceipt.observed 16
            (left.map SourceEqualityClassOrder.Record.paths ++
              right.map SourceEqualityClassOrder.Record.paths) := by
  cases first with
  | none => rfl
  | some left =>
      cases second with
      | none => rfl
      | some right =>
          cases left <;> cases right
          · rfl
          all_goals
            simp only [SourceEqualityPrecheck.combine]
            rw [← SourceCompactGuards.arrayNormalize_eq]
            exact array_small _

attribute [local cbv_eval] array_small eqGuard_small combine_small

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private noncomputable instance : DecidableEq (Value Symbol Guard) := by
  classical exact inferInstance

/-- Use the accepted original source in its exact ordinary-symbol representation. -/
def expression : Syntax Symbol Guard := SourceSynthesisUniverseCallerBoundary.expression

/-- Include the literal guards inside every original binder body in preparation order. -/
def originals : List Guard := SourceEqualityConstraintOrigins.guards expression

/-- The original signed request succeeds before the ordinary-symbol representation adapter. -/
theorem source_accepts :
    (SourceSynthesisFirstOrderConstruction.firstOrderRaw
      SourceSynthesisUniverseRequiredBoundary.library
      SourceSynthesisUniverseRequiredBoundary.query 2).map
        SourceSynthesisUniverseCallerBoundary.ordinarySymbols = .ok expression :=
  SourceSynthesisUniverseCallerBoundary.source_accepts

/-- Retain original construction, actual field allocation, and the current caller return. -/
structure Receipt where
  root : Value Symbol Guard
  heap : State Symbol Guard
  fields : List EqValue
  cache : Cache.State Key
  fault : SourceCurrentAllocatedPartialWorker.Fault 64
  state : SourceCurrentAllocatedPartialState.State 64

/-- Start the current worker with the returned original cache and its allocated empty inherited value. -/
noncomputable def observation : Option Receipt :=
  match SourceEqualityOriginalAllocationPreparation.prepare originals Cache.emptyState with
  | (.error _, _) => none
  | (.ok fields, cache) =>
      match InternedFreshOrdinaryConstruction.build expression [] empty with
      | .pending .. => none
      | .done root heap =>
          match SourceCurrentAllocatedPartialWorker.nodeCall
              10 8 8 8 8 8 8 24 8 128 10000
              ⟨SourceCurrentAllocatedPartialInitialization.emptyValue cache, root⟩
              (SourceCurrentAllocatedPartialInitialization.caller 64 cache heap) with
          | .done .. => none
          | .failed fault state => some ⟨root, heap, fields, cache, fault, state⟩

/-- A returned receipt records actual preparation, original construction, and the current execution. -/
theorem observation_receipts (observed : Receipt) (found : observation = some observed) :
    SourceEqualityOriginalAllocationPreparation.prepare originals Cache.emptyState =
        (.ok observed.fields, observed.cache) ∧
      InternedFreshOrdinaryConstruction.build expression [] empty = .done observed.root observed.heap ∧
      SourceCurrentAllocatedPartialWorker.nodeCall
        10 8 8 8 8 8 8 24 8 128 10000
        ⟨SourceCurrentAllocatedPartialInitialization.emptyValue observed.cache, observed.root⟩
        (SourceCurrentAllocatedPartialInitialization.caller 64 observed.cache observed.heap) =
          .failed observed.fault observed.state := by
  unfold observation at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases found
  exact ⟨by assumption, by assumption, by assumption⟩

/-- Identify the application and function in their actual published current requests. -/
def RequestFacts (observed : Receipt) (owner application function : NodeRequest) : Prop :=
  owner.value.referenceOf = observed.root.referenceOf ∧
  SourceSynthesisUniverseCallerBoundary.headName application.value = some ("app", .top) ∧
  SourceSynthesisUniverseCallerBoundary.headName function.value = some ("f", .top) ∧
  SourceSynthesisUniverseRequiredBoundary.transparentHeight application.value = 2 ∧
  SourceSynthesisUniverseRequiredBoundary.transparentHeight function.value = 4

private instance (observed : Receipt) (owner application function : NodeRequest) :
    Decidable (RequestFacts observed owner application function) := by
  unfold RequestFacts
  infer_instance

/-- Read only actual evaluating cells and their allocated inherited payloads. -/
noncomputable def certificate : Bool :=
  match observation with
  | none => false
  | some observed =>
      match observed.state.nodeResults.cells 0, observed.state.nodeResults.cells 2,
          observed.state.nodeResults.cells 4 with
      | some ⟨owner, .evaluating⟩, some ⟨application, .evaluating⟩, some ⟨function, .evaluating⟩ =>
          decide (RequestFacts observed owner application function) &&
            SourceEqualityPrecheck.isEmpty application.inherited.payload &&
            SourceEqualityPrecheck.isEmpty function.inherited.payload
      | _, _, _ => false

/-- Kernel evaluation checks the actual current requests and their source-derived inherited values. -/
theorem actual : certificate = true := by
  cbv

/-- No completed fourth-memo entry appears during this actual current prefix. -/
theorem actual_fourth_empty : observation.map (fun observed => observed.state.fourth) =
    some SourceCurrentEmptinessMemo.empty := by
  cbv

/-- Actual evaluating owners retain the larger function and the empty fourth memo. -/
theorem actual_requests : ∃ observed owner application function,
    observation = some observed ∧
    observed.state.nodeResults.cells 0 = some ⟨owner, .evaluating⟩ ∧
    observed.state.nodeResults.cells 2 = some ⟨application, .evaluating⟩ ∧
    observed.state.nodeResults.cells 4 = some ⟨function, .evaluating⟩ ∧
    RequestFacts observed owner application function ∧
    SourceEqualityPrecheck.isEmpty application.inherited.payload = true ∧
    SourceEqualityPrecheck.isEmpty function.inherited.payload = true ∧
    observed.state.fourth = SourceCurrentEmptinessMemo.empty := by
  cases found : observation with
  | none =>
      have checked := actual
      simp only [certificate, found, Bool.false_eq_true] at checked
  | some observed =>
      have checked := actual
      simp only [certificate, found] at checked
      split at checked <;> try contradiction
      simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
      have fourth : observed.state.fourth = SourceCurrentEmptinessMemo.empty := by
        simpa only [found, Option.map_some, Option.some.injEq] using actual_fourth_empty
      exact ⟨observed, _, _, _, rfl, by assumption, by assumption, by assumption,
        checked.1.1, checked.1.2, checked.2, fourth⟩

/-- Current inherited propagation still requests a function taller than its application. -/
theorem requested_function_exceeds_application : ∃ observed owner application function,
    observation = some observed ∧
    observed.state.nodeResults.cells 2 = some ⟨application, .evaluating⟩ ∧
    observed.state.nodeResults.cells 4 = some ⟨function, .evaluating⟩ ∧
    RequestFacts observed owner application function ∧
    SourceEqualityPrecheck.isEmpty function.inherited.payload = true ∧
    observed.state.fourth = SourceCurrentEmptinessMemo.empty ∧
    SourceSynthesisUniverseRequiredBoundary.transparentHeight application.value <
      SourceSynthesisUniverseRequiredBoundary.transparentHeight function.value := by
  obtain ⟨observed, owner, application, function, found, _root, appCell, functionCell,
    facts, _appInherited, functionInherited, fourth⟩ := actual_requests
  exact ⟨observed, owner, application, function, found, appCell, functionCell,
    facts, functionInherited, fourth, by
      unfold RequestFacts at facts
      have appHeight := facts.2.2.2.1
      have functionHeight := facts.2.2.2.2
      omega⟩

end MicroCFTA.SourceSynthesisUniverseCurrentCallerBoundary

import MicroCFTA.SourceSynthesisUniverseNarrowedBoundary
import MicroCFTA.SourceEqualityPartialMemoWorker

/-!
# An actual recursive caller requests the larger function

The original FirstOrder request is the verified one-component size-two input.
Ordinary source symbols have refinement Top. The syntax adapter below keeps
each original name and adds that refinement, as Symbol.hs constructs Symbol.
It preserves every guard, child order, union, and binder instruction.

The modeled recursive memo worker starts at this freshly built root. Its
actual inherited combination and trie descent supply every child payload.
The native memo-key model uses 64-bit words, as on the current x86_64 host.
The observation stops at an exhausted inner request. Published ancestor
cells retain the application and function requests. No recording callback
replaces a recursive call. This is a bounded caller-prefix witness. It does
not identify its heap with the String-only fixture or prove whole-call
termination or native Haskell scheduling.
-/
namespace MicroCFTA.SourceSynthesisUniverseCallerBoundary
open InternedConstructorTemplates InternedNestedConstruction
open SourceSynthesisGeneralizeSyntax (Guard top)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

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

mutual
/-- Add the source ordinary-symbol Top refinement to every original name. -/
def ordinarySymbols : Syntax String Guard → Syntax Symbol Guard
  | .empty => .empty
  | .var index => .var index
  | .node edges => .node (ordinaryEdges edges)
  | .union values => .union (ordinaryChildren values)
  | .binder smart body => .binder smart (ordinarySymbols body)

/-- Preserve the complete source order of child instructions. -/
def ordinaryChildren : List (Syntax String Guard) → List (Syntax Symbol Guard)
  | [] => []
  | first :: rest => ordinarySymbols first :: ordinaryChildren rest

/-- Preserve each source edge guard and child list while refining only its name. -/
def ordinaryEdges : List (EdgeSyntax String Guard) → List (EdgeSyntax Symbol Guard)
  | [] => []
  | .mk name guard children :: rest =>
      .mk (name, .top) guard (ordinaryChildren children) :: ordinaryEdges rest
end

/-- Execute the actual original source expression in the ordinary-symbol representation. -/
def expression : Syntax Symbol Guard :=
  ordinarySymbols SourceSynthesisUniverseRequiredBoundary.expression

/-- The original signed source request succeeds before the exact symbol representation adapter. -/
theorem source_accepts :
    (SourceSynthesisFirstOrderConstruction.firstOrderRaw
      SourceSynthesisUniverseRequiredBoundary.library
      SourceSynthesisUniverseRequiredBoundary.query 2).map ordinarySymbols = .ok expression := by
  rw [SourceSynthesisUniverseRequiredBoundary.source_accepts]
  rfl

/-- Retain construction and the actual incomplete recursive request with all published cells. -/
structure Receipt where
  root : Value Symbol Guard
  heap : State Symbol Guard
  exhausted : SourceEqualityPartialMemoWorker.Request
  handle : Nat
  state : SourceEqualityPartialMemoWorker.State 64

/-- Run the real recursive worker from the original root and empty caller memo tables. -/
noncomputable def observation : Option Receipt :=
  match InternedFreshOrdinaryConstruction.build expression [] empty with
  | .pending .. => none
  | .done root heap =>
      match SourceEqualityPartialMemoWorker.run 8 8 8 8 8 128 3 (some []) root
          (SourceEqualityPartialMemoWorker.initial (SourceEqualityNativeInitial.cold 64 heap)) with
      | .incomplete (.exhausted exhausted handle state) => some ⟨root, heap, exhausted, handle, state⟩
      | _ => none

/-- A returned receipt records the original build and the literal bounded recursive run. -/
theorem observation_receipts (observed : Receipt) (found : observation = some observed) :
    InternedFreshOrdinaryConstruction.build expression [] empty = .done observed.root observed.heap ∧
      SourceEqualityPartialMemoWorker.run 8 8 8 8 8 128 3 (some []) observed.root
        (SourceEqualityPartialMemoWorker.initial (SourceEqualityNativeInitial.cold 64 observed.heap)) =
          .incomplete (.exhausted observed.exhausted observed.handle observed.state) := by
  unfold observation at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases found
  exact ⟨by assumption, by assumption⟩

/-- Read a source name only from an actual one-row ordinary node. -/
def headName : Value Symbol Guard → Option Symbol
  | .node _ [edge] _ _ => some edge.entry.key.symbol
  | _ => none

/-- Read the actual sole row's ordered children without exposing recursive Mu bodies. -/
def rowChildren : Value Symbol Guard → List (Value Symbol Guard)
  | .node _ [edge] _ _ => edge.children
  | _ => []

/-- These observations identify the published application and its larger function request. -/
def RequestFacts (observed : Receipt)
    (owner application function : SourceEqualityPartialMemoWorker.Request) : Prop :=
  owner.value.referenceOf = observed.root.referenceOf ∧
  headName application.value = some ("app", .top) ∧
  headName function.value = some ("f", .top) ∧
  SourceSynthesisUniverseRequiredBoundary.transparentHeight application.value = 2 ∧
  SourceSynthesisUniverseRequiredBoundary.transparentHeight function.value = 4 ∧
  observed.exhausted.value.referenceOf =
    ((rowChildren function.value)[0]?.getD (.empty : Value Symbol Guard)).referenceOf

private instance (observed : Receipt)
    (owner application function : SourceEqualityPartialMemoWorker.Request) :
    Decidable (RequestFacts observed owner application function) := by
  unfold RequestFacts
  infer_instance

/-- Check actual published cells and their computed inherited payloads after real recursive calls. -/
noncomputable def certificate : Bool :=
  match observation with
  | none => false
  | some observed =>
      match observed.state.memo.cells 0, observed.state.memo.cells 2, observed.state.memo.cells 4 with
      | some ⟨owner, .evaluating⟩, some ⟨application, .evaluating⟩, some ⟨function, .evaluating⟩ =>
          decide (RequestFacts observed owner application function) &&
            SourceEqualityPrecheck.isEmpty application.inherited &&
            SourceEqualityPrecheck.isEmpty function.inherited
      | _, _, _ => false

/-- Kernel evaluation checks the actual caller requests and their source-derived inherited payloads. -/
theorem actual : certificate = true := by
  cbv

/-- The reached application and function requests retain their original evaluating memo cells. -/
theorem actual_requests : ∃ observed owner application function,
    observation = some observed ∧
    observed.state.memo.cells 0 = some ⟨owner, .evaluating⟩ ∧
    observed.state.memo.cells 2 = some ⟨application, .evaluating⟩ ∧
    observed.state.memo.cells 4 = some ⟨function, .evaluating⟩ ∧
    RequestFacts observed owner application function ∧
    SourceEqualityPrecheck.isEmpty application.inherited = true ∧
    SourceEqualityPrecheck.isEmpty function.inherited = true := by
  have checked := actual
  unfold certificate at checked
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨_, _, _, _, by assumption, by assumption, by assumption, by assumption,
    checked.1.1, checked.1.2, checked.2⟩

/-- Actual source inheritance still permits a requested function taller than its application. -/
theorem requested_function_exceeds_application : ∃ observed owner application function,
    observation = some observed ∧
    observed.state.memo.cells 2 = some ⟨application, .evaluating⟩ ∧
    observed.state.memo.cells 4 = some ⟨function, .evaluating⟩ ∧
    RequestFacts observed owner application function ∧
    SourceEqualityPrecheck.isEmpty function.inherited = true ∧
    SourceSynthesisUniverseRequiredBoundary.transparentHeight application.value <
      SourceSynthesisUniverseRequiredBoundary.transparentHeight function.value := by
  obtain ⟨observed, owner, application, function, found, _root, appCell, functionCell,
    facts, _appInherited, functionInherited⟩ := actual_requests
  exact ⟨observed, owner, application, function, found, appCell, functionCell,
    facts, functionInherited, by
      unfold RequestFacts at facts
      have appHeight := facts.2.2.2.1
      have functionHeight := facts.2.2.2.2.1
      omega⟩

end MicroCFTA.SourceSynthesisUniverseCallerBoundary

import MicroCFTA.SourceSynthesisUniverseRequiredBoundary

/-!
# Complete application narrowing can exceed its original ordinary height

The input is the verified original one-component library and size-two query.
Its actual filter pass supplies the application and native caches. The next
observation runs the application's complete equality pass, including its
required paths, every selected class, and final empty propagation.

The measured function child retains its exposed type arrow after that pass.
Its final height is four. The original application height is two, and the
preceding required-path stage returns function height three. This refutes
the proposed strict height decrease at the returned child. It does not
prove a next recursive request or a native Haskell counterexample.
-/
namespace MicroCFTA.SourceSynthesisUniverseNarrowedBoundary
open InternedConstructorTemplates InternedNestedConstruction
open SourceSynthesisGeneralizeSyntax (Guard top)

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

private noncomputable def unconstrained (value : Value String Guard) : Bool :=
  InternedSourceCrush.unconstrained SourceMemoGate.plain value

/-- Run the complete application pass from its actual pre-selection native state. -/
noncomputable def applicationPass (original : SourceSynthesisUniverseRequiredBoundary.Receipt) :
    SourceEqualityOnePassWorker.Result 8 String Guard :=
  SourceEqualityOnePassWorker.run unconstrained top SourceEqualityPCSNativeEdge.conjoin
    SourceMemoGate.plain top 8 8 8 8 8 128 (some original.records) (some [])
    original.applicationRow.children original.native

/-- Retain the actual original receipt, returned child list, and final native state. -/
structure Receipt where
  original : SourceSynthesisUniverseRequiredBoundary.Receipt
  narrowed : List (Value String Guard)
  final : SourceRecursiveIntersectionThunks.State 8 String Guard

/-- Observe only completed successful application passes over the actual original receipt. -/
noncomputable def observation : Option Receipt :=
  match SourceSynthesisUniverseRequiredBoundary.observation with
  | none => none
  | some original => match applicationPass original with
    | .done (.ok narrowed) final => some ⟨original, narrowed, final⟩
    | _ => none

/-- Keep the original source equations and the complete application-pass equation. -/
def Receipts (observed : Receipt) : Prop :=
  SourceSynthesisUniverseRequiredBoundary.observation = some observed.original ∧
  SourceSynthesisUniverseRequiredBoundary.Receipts observed.original ∧
  applicationPass observed.original = .done (.ok observed.narrowed) observed.final

/-- Every successful observation records the complete pass over a verified original input. -/
theorem observation_receipts (observed : Receipt) (found : observation = some observed) :
    Receipts observed := by
  unfold observation at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases found
  exact ⟨by assumption,
    SourceSynthesisUniverseRequiredBoundary.observation_receipts _ (by assumption),
    by assumption⟩

/-- Read original application height, returned function height, and its exposed arrow. -/
def summary (observed : Receipt) : Nat × Nat × Bool :=
  (SourceSynthesisUniverseRequiredBoundary.transparentHeight observed.original.application,
    SourceSynthesisUniverseRequiredBoundary.transparentHeight
      (SourceSynthesisUniverseRequiredBoundary.functionValue observed.narrowed),
    SourceSynthesisUniverseRequiredBoundary.arrowAnnotations
      (SourceSynthesisUniverseRequiredBoundary.functionValue observed.narrowed))

/-- Kernel evaluation follows the original construction and both complete equality passes. -/
theorem actual_summary : observation.map summary = some (2, 4, true) := by
  cbv

/-- Complete application narrowing can return a child taller than its original application. -/
theorem narrowed_child_exceeds_application : ∃ observed,
    observation = some observed ∧ Receipts observed ∧
    SourceSynthesisUniverseRequiredBoundary.transparentHeight observed.original.application <
      SourceSynthesisUniverseRequiredBoundary.transparentHeight
        (SourceSynthesisUniverseRequiredBoundary.functionValue observed.narrowed) ∧
    SourceSynthesisUniverseRequiredBoundary.arrowAnnotations
      (SourceSynthesisUniverseRequiredBoundary.functionValue observed.narrowed) = true := by
  cases found : observation with
  | none =>
      have impossible := actual_summary
      simp only [found, Option.map_none, reduceCtorEq] at impossible
  | some observed =>
      have checked : summary observed = (2, 4, true) := by
        simpa only [found, Option.map_some, Option.some.injEq] using actual_summary
      have parent := congrArg (fun result => result.1) checked
      have child := congrArg (fun result => result.2.1) checked
      have exposed := congrArg (fun result => result.2.2) checked
      refine ⟨observed, rfl, observation_receipts observed found, ?_, exposed⟩
      change SourceSynthesisUniverseRequiredBoundary.transparentHeight observed.original.application = 2 at parent
      change SourceSynthesisUniverseRequiredBoundary.transparentHeight
        (SourceSynthesisUniverseRequiredBoundary.functionValue observed.narrowed) = 4 at child
      omega

/-- Original application height cannot justify every returned narrowed-child request. -/
theorem not_narrowed_child_descent : ¬ (∀ observed, observation = some observed →
    SourceSynthesisUniverseRequiredBoundary.transparentHeight
        (SourceSynthesisUniverseRequiredBoundary.functionValue observed.narrowed) <
      SourceSynthesisUniverseRequiredBoundary.transparentHeight observed.original.application) := by
  intro decrease
  obtain ⟨observed, found, _receipts, increased, _exposed⟩ := narrowed_child_exceeds_application
  have smaller := decrease observed found
  omega

end MicroCFTA.SourceSynthesisUniverseNarrowedBoundary

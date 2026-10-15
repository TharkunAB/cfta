import MicroCFTA.SourceEqualityDemandTargetLanguage

/-!
# Finite target construction from actual demand-prefix checks

Projection and general merging complete locally. Native word checks refer
only to the actual operand demand and completed recursive fold. They do
not supply a completed target or a whole-worker progress law.
-/
namespace MicroCFTA.SourceEqualityDemandTargetComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityDemandTarget

/-- A finite fold plan checks native words only after actual operand and tail prefixes. -/
inductive FoldRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) : List (List Int) →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | nil : FoldRanges emptyGuard conjoin clear top values seed [] state
  | cons
      (rest : ∀ value middle, Operand clear top path values before value middle → FoldRanges emptyGuard conjoin clear top values seed paths middle)
      (step : ∀ value middle, Operand clear top path values before value middle → ∀ tail later,
        Fold emptyGuard conjoin clear top values seed paths middle tail later →
        SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
          (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) later) :
      FoldRanges emptyGuard conjoin clear top values seed (path :: paths) before

/-- Target lists retain the actual empty and first-seeded source branches in their word checks. -/
def TargetRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  match paths with
  | [] => True
  | seed :: rest => FoldRanges emptyGuard conjoin clear top values seed rest before

/-- Actual local operand progress and idle warm native progress derive complete finite source folds. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin before)
    (ranges : FoldRanges emptyGuard conjoin clear top values seed paths before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ result after, Fold emptyGuard conjoin clear top values seed paths before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] := by
  induction paths generalizing before with
  | nil =>
      obtain ⟨result, after, operand, finalReady, keeps, resultAvailable, resultClosed, _⟩ :=
        SourceEqualityTargetOperand.complete emptyGuard conjoin clear top seed values before ready available closed
      exact ⟨result, after, .nil operand, finalReady, keeps, resultAvailable, resultClosed⟩
  | cons path paths ih =>
      cases ranges with
      | cons restPlan stepPlan =>
          obtain ⟨value, middle, operand, middleReady, firstKeeps, valueAvailable, valueClosed, _⟩ :=
            SourceEqualityTargetOperand.complete emptyGuard conjoin clear top path values before ready available closed
          obtain ⟨tail, later, rest, laterReady, restKeeps, tailAvailable, tailClosed⟩ := ih middle middleReady (restPlan value middle operand)
            (fun value member => firstKeeps.available value (available value member))
          obtain ⟨result, after, step, finalReady, stepKeeps, resultAvailable, resultClosed, _⟩ := SourceEqualityNativeScoped.complete
            emptyGuard conjoin later laterReady value tail (restKeeps.available value valueAvailable) tailAvailable valueClosed tailClosed
            (stepPlan value middle operand tail later rest) (fun _ _ => true) (fun _ _ _ => rfl)
          exact ⟨result, after, .cons operand rest step, finalReady, firstKeeps.trans (restKeeps.trans stepKeeps), resultAvailable, resultClosed⟩

/-- Every finite requested source target completes from its actual-prefix native word checks. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (ranges : TargetRanges emptyGuard conjoin clear top values paths before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ result after, Target emptyGuard conjoin clear top values paths before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] := by
  cases paths with
  | nil => exact ⟨.empty, before, .nil, ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons seed paths =>
      obtain ⟨result, after, trace, checked⟩ := fold_complete emptyGuard conjoin clear top values seed paths before ready ranges available closed
      exact ⟨result, after, .cons trace, checked⟩

end MicroCFTA.SourceEqualityDemandTargetComplete

import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.SourcePruningNativeViewObservedOrdinary
import MicroCFTA.MergedOrdinaryHeight

/-!
# Actual recursive boundaries retain their original narrowing input

Fallback narrowing produces only ordinary values.
A completed Mu or Union result must use a retained input branch.
The value and native heap then equal their original inputs.
-/
namespace MicroCFTA.SourcePruningOuterNarrow
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Typing Key : Type}

/-- An actual completed boundary result retains its original full value and native heap. -/
theorem narrow_boundary_retained [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (observed : narrow holeKey fits admits metadata fuel uv value before = .done result after)
    (boundary : MergedOrdinaryHeight.recursiveBoundary result = true) :
    result = value ∧ after = before := by
  cases value with
  | mu entry body depth ordinary =>
      have same := MergedSourceComparison.Result.done.inj observed
      exact ⟨same.1.symm, same.2.symm⟩
  | empty | reference | node | union =>
      simp only [narrow] at observed
      split at observed
      · have same := MergedSourceComparison.Result.done.inj observed
        exact ⟨same.1.symm, same.2.symm⟩
      · have ordinary := SourcePruningNativeView.narrowAt_done_ordinary
          fits admits fuel (holeKey metadata.typing uv) _ before result after
          ready available closed observed
        cases result <;> simp_all only [SourceEqualityRequiredCache.Ordinary,
          MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true]

end MicroCFTA.SourcePruningOuterNarrow

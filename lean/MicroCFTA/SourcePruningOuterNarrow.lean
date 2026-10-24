import MicroCFTA.SourcePruningRecordTypes
import MicroCFTA.SourcePruningNativeView

namespace MicroCFTA.SourcePruningOuterNarrow
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Typing Key : Type}

/-- Retain Mu and raw type positions. Narrow each other value at its original key. -/
def narrow [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard) :
    MergedSourceComparison.Result Symbol Guard (Value Symbol Guard)
 :=
  match value with
  | .mu .. => .done value before
  | _ =>
      if metadata.types.contains uv then .done value before
      else SourcePruningNativeView.narrowAt fits admits fuel (holeKey metadata.typing uv) value before

/-- Every fuel retains the complete Mu value and the same heap. -/
theorem narrow_mu [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing) (fuel uv : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depthShape ordinaryShape : Value Symbol Guard) (before : State Symbol Guard) :
    narrow holeKey fits admits metadata fuel uv (.mu entry body depthShape ordinaryShape) before =
      .done (.mu entry body depthShape ordinaryShape) before
 := by
  rfl

/-- Incoming raw type membership retains every complete value and the same heap. -/
theorem narrow_type [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (inside : uv ∈ metadata.types) :
    narrow holeKey fits admits metadata fuel uv value before = .done value before
 := by
  cases value with
  | mu => rfl
  | empty | reference | node | union => simp [narrow, inside]

/-- Every other input calls the existing narrowAt at the original raw key. -/
theorem narrow_fallback [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (notMu : ∀ entry body depthShape ordinaryShape, value ≠ .mu entry body depthShape ordinaryShape)
    (outside : uv ∉ metadata.types) :
    narrow holeKey fits admits metadata fuel uv value before =
      SourcePruningNativeView.narrowAt fits admits fuel (holeKey metadata.typing uv) value before
 := by
  cases value with
  | mu entry body depthShape ordinaryShape =>
      exact False.elim (notMu entry body depthShape ordinaryShape rfl)
  | empty | reference | node | union => simp [narrow, outside]

/-- Ready closed inputs derive a completed run and retain that run at larger fuel. -/
theorem narrow_complete [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = []) :
    ∃ fuel result after,
      narrow holeKey fits admits metadata fuel uv value before = .done result after ∧
      SourceEqualityRequiredCache.Keeps before after ∧ Available after result ∧ result.free = [] ∧
      (∀ extra, narrow holeKey fits admits metadata (fuel + extra) uv value before = .done result after)
 := by
  cases value with
  | mu entry body depthShape ordinaryShape =>
      refine ⟨0, .mu entry body depthShape ordinaryShape, before, rfl,
        SourceEqualityRequiredCache.pure_keeps before ready, available, closed, ?_⟩
      intro extra
      rfl
  | empty | reference | node | union =>
      by_cases inTypes : uv ∈ metadata.types
      · refine ⟨0, _, before, ?_, SourceEqualityRequiredCache.pure_keeps before ready,
          available, closed, ?_⟩
        · simp [narrow, inTypes]
        · intro extra
          simp [narrow, inTypes]
      · obtain ⟨fuel, _rows, _middle, result, after, _exposed, _built, narrowed, kept,
            resultAvailable, resultClosed, _ordinary, _resultRows, _secondRead,
            _emptyIff, _rowsEmptyIff, stable⟩ :=
          SourcePruningNativeView.narrowAt_complete fits admits (holeKey metadata.typing uv) _ before
            ready available closed
        refine ⟨fuel, result, after, ?_, kept, resultAvailable, resultClosed, ?_⟩
        · simpa [narrow, inTypes] using narrowed
        · intro extra
          simpa [narrow, inTypes] using stable extra

end MicroCFTA.SourcePruningOuterNarrow

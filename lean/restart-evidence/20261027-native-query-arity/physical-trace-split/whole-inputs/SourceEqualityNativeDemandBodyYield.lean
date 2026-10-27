import MicroCFTA.SourceEqualityNativeDemandContinuation

/-!
# Code emitted by actual checked edge bodies

Every yielded body branch emits source code at its exact checked state.
An appended continuation changes that code, not the branch or its state.
-/

namespace MicroCFTA.SourceEqualityNativeDemandBodyYield

open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat} {Output : Type}

/-- A yielded appended body exposes the same pure-body code and the same full checked state. -/
theorem yielded_unbind (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (before after : State width) (control : Control Output)
    (one : body request next before = .yielded control after) :
    ∃ code, body request .pure before = .yielded (.code code) after ∧
      control = .code (code.bind next) := by
  unfold body at one
  split at one
  · cases one
    refine ⟨SourceEqualityNativeCheckedCode.sentinel request.left, ?_, rfl⟩
    simp_all [body, sentinel, code_bind_pure]
  · split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · cases one
          refine ⟨SourceEqualityNativeCheckedCode.sentinel request.left, ?_, rfl⟩
          simp_all [body, sentinel, code_bind_pure]
        · cases one
          refine ⟨SourceEqualityNativeCheckedCode.sentinel request.left, ?_, rfl⟩
          simp_all [body, sentinel, code_bind_pure]
        · cases one
          refine ⟨_, ?_, rfl⟩
          simp_all [body, code_bind_pure]

/-- A yielded pure body always exposes an ordinary code control. -/
theorem pure_yielded_code (request : EdgeRequest Symbol Guard)
    (before after : State width) (control : Control (EdgeValue Symbol Guard))
    (one : body request .pure before = .yielded control after) :
    ∃ code, control = .code code := by
  obtain ⟨code, _, same⟩ := yielded_unbind request Code.pure before after control one
  exact ⟨code, by simpa only [code_bind_pure] using same⟩

end MicroCFTA.SourceEqualityNativeDemandBodyYield

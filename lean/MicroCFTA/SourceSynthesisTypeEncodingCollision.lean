import MicroCFTA.SourceSynthesisTypeSubstitutionWitnesses

/-!
# Reserved type-encoding collision

Distinct raw types can have the same native annotation.
The constant leaf in this example fails AliasSafe.
The result concerns the unrestricted raw source model.
Haskell frontend reachability remains a separate question.
-/
namespace MicroCFTA.SourceSynthesisTypeEncodingCollision
open SourceSynthesisTypeSyntax
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisTypeSubstitutionWitnesses (AliasSafe)

/-- A reserved constant aliases a raw variable in the actual native encoding. -/
theorem reserved_variable_constant_collision :
    Ty.tVar "a" ≠ Ty.tCons "var1" [] ∧
      rigidTerm (Ty.tVar "a") = rigidTerm (Ty.tCons "var1" []) ∧
      ¬AliasSafe (Ty.tCons "var1" []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro same
    cases same
  · simp [rigidTerm, variableSymbol]
  · intro safe
    rw [AliasSafe] at safe
    have rejected := safe.1 rfl
    change true = false at rejected
    cases rejected

end MicroCFTA.SourceSynthesisTypeEncodingCollision

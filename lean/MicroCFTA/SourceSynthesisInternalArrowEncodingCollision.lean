import MicroCFTA.SourceSynthesisOrdinaryTyping

/-!
# Internal arrow layout collides with an alias-safe raw constructor

The current compatibility predicate does not reserve the complete arrow
layout. A raw function and an ordinary three-child constructor can satisfy
AliasSafe and have equal encodings while ordinary normalization keeps them
distinct. This law concerns type encoding only. It supplies no source
acceptance, Haskell execution, or public input restriction.
-/
namespace MicroCFTA.SourceSynthesisInternalArrowEncodingCollision
open SourceSynthesisTypeSyntax (Ty)
open SourceSynthesisGeneralizeSyntax (isVariableSymbol)
open SourceSynthesisTypeSubstitutionWitnesses (AliasSafe)
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisOrdinaryTyping (Equivalent normalizeTy)

private theorem constant_safe (name : String) (notVariable : isVariableSymbol name = false) :
    AliasSafe (Ty.tCons name []) := by
  rw [AliasSafe]
  exact ⟨fun _empty => notVariable, fun _child member => nomatch member⟩

/-- AliasSafe does not make rigid encoding reflect ordinary type equality. -/
theorem internal_arrow_constructor_collision :
    AliasSafe (Ty.tFun (.tCons "A" []) (.tCons "B" [])) ∧
      AliasSafe (Ty.tCons "->" [.tCons "(->)" [], .tCons "A" [], .tCons "B" []]) ∧
      rigidTerm (Ty.tFun (.tCons "A" []) (.tCons "B" [])) =
        rigidTerm (Ty.tCons "->" [.tCons "(->)" [], .tCons "A" [], .tCons "B" []]) ∧
      ¬Equivalent (Ty.tFun (.tCons "A" []) (.tCons "B" []))
        (Ty.tCons "->" [.tCons "(->)" [], .tCons "A" [], .tCons "B" []]) := by
  have firstSafe : AliasSafe (Ty.tCons "A" []) := constant_safe "A" rfl
  have secondSafe : AliasSafe (Ty.tCons "B" []) := constant_safe "B" rfl
  have markerSafe : AliasSafe (Ty.tCons "(->)" []) := constant_safe "(->)" (by
    have notPrefix : "(->)".startsWith "var_" = false := by
      apply String.startsWith_string_eq_false_iff.mpr
      change ¬ (['v', 'a', 'r', '_'] <+: ['(', '-', '>', ')'])
      decide
    simp [isVariableSymbol, notPrefix])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [AliasSafe]
    exact ⟨firstSafe, secondSafe⟩
  · rw [AliasSafe]
    constructor
    · intro impossible
      cases impossible
    · intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact markerSafe
      rcases List.mem_cons.mp member with rfl | member
      · exact firstSafe
      have same := List.mem_singleton.mp member
      subst child
      exact secondSafe
  · simp [rigidTerm]
  · simp [Equivalent, normalizeTy]

end MicroCFTA.SourceSynthesisInternalArrowEncodingCollision

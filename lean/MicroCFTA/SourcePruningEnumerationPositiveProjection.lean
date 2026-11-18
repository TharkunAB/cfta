import MicroCFTA.SourcePruningEnumerationConstraint

namespace MicroCFTA.SourcePruningEnumerationConstraint
set_option autoImplicit false

theorem project_positive_residual_none
    {Formula : Type}
    (constraint : SourceSymbolicIndex.Constraint Formula)
    (positiveGuard : (SourceCompactGuards.positive constraint.guard).isSome = true)
    (tries : List EqualityTrie.Trie)
    (residual : Option (SourceSymbolicIndex.Constraint Formula))
    (projected : project constraint = some (tries, residual)) :
    residual = none
 := by
  cases source : SourceCompactGuards.sourceEqualities constraint with
  | none =>
      simp only [project, source] at projected
      cases projected
  | some classes =>
      have canonical : project constraint = some (EnumerationEquality.readClasses classes, none) := by
        simp only [project, source, positiveGuard, ↓reduceIte]
      exact (congrArg Prod.snd (Option.some.inj (canonical.symm.trans projected))).symm

end MicroCFTA.SourcePruningEnumerationConstraint

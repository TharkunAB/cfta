import MicroCFTA.SourceCurrentEqualityNormalizationFixed

/-!
# Child separation under completed equality classes

At a congruence fixed point, a finite chain of class-prefix replacements
reduces to one replacement with a common suffix. If each class has at most
one path through a chosen child, that child's distinct paths stay distinct.
These results concern path geometry. They make no execution support claim.
-/
namespace MicroCFTA.SourceCurrentNormalizedChildSeparation
open EqualityNormalize

/-- Class equalities act on a common suffix; finite chains retain that relation. -/
inductive Rel (classes : Constraints) : Path → Path → Prop where
  /-- Every path is equal to itself. -/
  | refl (path : Path) : Rel classes path path
  /-- Two paths in one class retain a common appended suffix. -/
  | member (paths : Class) (selected : paths ∈ classes)
      (left right : Path) (first : left ∈ paths) (second : right ∈ paths) (suffix : Path) :
      Rel classes (left ++ suffix) (right ++ suffix)
  /-- Two finite equality chains compose at their shared path. -/
  | trans (first : Rel classes left middle) (second : Rel classes middle right) :
      Rel classes left right

private def One (classes : Constraints) (left right : Path) : Prop :=
  left = right ∨ ∃ paths ∈ classes, ∃ a ∈ paths, ∃ b ∈ paths, ∃ suffix,
    left = a ++ suffix ∧ right = b ++ suffix

private theorem extension_into {classes : Constraints}
    (fixed : congruenceStep classes = some classes) {first second : Class}
    (firstMember : first ∈ classes) (secondMember : second ∈ classes)
    {base suffix : Path} (initial : base ∈ first) (extended : base ++ suffix ∈ second) :
    ∀ path ∈ first, path ++ suffix ∈ second := by
  have disjoint := congruenceStep_disjoint classes classes fixed
  by_cases empty : suffix = []
  · subst suffix
    have common : base ∈ second := by simpa only [List.append_nil] using extended
    have same := components_equal classes disjoint first second firstMember secondMember base initial common
    subst second
    intro path member
    simpa only [List.append_nil] using member
  · have requested : suffix ∈ suffixes first classes :=
      (mem_suffixes suffix first classes).mpr ⟨base, initial, base ++ suffix,
        (mem_members _ _).mpr ⟨second, secondMember, extended⟩, empty, rfl⟩
    obtain ⟨output, outputMember, included⟩ :=
      fixedPoint_congruence_closed classes fixed first firstMember suffix requested
    have same := components_equal classes disjoint output second outputMember secondMember
      (base ++ suffix) (included base initial) extended
    subst output
    exact included

private theorem one_trans {classes : Constraints}
    (fixed : congruenceStep classes = some classes) {left middle right : Path}
    (first : One classes left middle) (second : One classes middle right) :
    One classes left right := by
  rcases first with same | ⟨firstClass, firstMember, a, aMember, b, bMember, firstSuffix, leftSame, middleSame⟩
  · subst middle
    exact second
  rcases second with same | ⟨secondClass, secondMember, c, cMember, d, dMember, secondSuffix, nextSame, rightSame⟩
  · subst right
    exact .inr ⟨firstClass, firstMember, a, aMember, b, bMember, firstSuffix, leftSame, middleSame⟩
  have common : b ++ firstSuffix = c ++ secondSuffix := middleSame.symm.trans nextSame
  have comparable : b.IsPrefix c ∨ c.IsPrefix b :=
    List.prefix_or_prefix_of_prefix (⟨firstSuffix, middleSame.symm⟩ : b.IsPrefix middle)
      (⟨secondSuffix, nextSame.symm⟩ : c.IsPrefix middle)
  rcases comparable with ⟨extra, extended⟩ | ⟨extra, extended⟩
  · have tails : firstSuffix = extra ++ secondSuffix := by
      apply List.append_cancel_left (as := b)
      simpa only [List.append_assoc] using
        common.trans (congrArg (fun path => path ++ secondSuffix) extended.symm)
    have located : b ++ extra ∈ secondClass := extended.symm ▸ cMember
    have included := extension_into fixed firstMember secondMember bMember located
    refine .inr ⟨secondClass, secondMember, a ++ extra, included a aMember,
      d, dMember, secondSuffix, ?_, rightSame⟩
    simpa only [tails, List.append_assoc] using leftSame
  · have tails : secondSuffix = extra ++ firstSuffix := by
      apply List.append_cancel_left (as := c)
      simpa only [List.append_assoc] using
        common.symm.trans (congrArg (fun path => path ++ firstSuffix) extended.symm)
    have located : c ++ extra ∈ firstClass := extended.symm ▸ bMember
    have included := extension_into fixed secondMember firstMember cMember located
    refine .inr ⟨firstClass, firstMember, a, aMember,
      d ++ extra, included d dMember, firstSuffix, leftSame, ?_⟩
    simpa only [tails, List.append_assoc] using rightSame

/-- Actual congruence completion reduces any finite equality chain to one class-prefix replacement. -/
theorem single {classes : Constraints} (fixed : congruenceStep classes = some classes)
    {left right : Path} (related : Rel classes left right) :
    left = right ∨ ∃ paths ∈ classes, ∃ a ∈ paths, ∃ b ∈ paths, ∃ suffix,
      left = a ++ suffix ∧ right = b ++ suffix := by
  change One classes left right
  induction related with
  | refl => exact .inl rfl
  | member paths selected left right first second suffix =>
    exact .inr ⟨paths, selected, left, first, right, second, suffix, rfl, rfl⟩
  | trans _ _ first second => exact one_trans fixed first second

private theorem rel_symm {classes : Constraints} {left right : Path}
    (related : Rel classes left right) : Rel classes right left := by
  induction related with
  | refl => exact .refl _
  | member paths selected left right first second suffix =>
    exact .member paths selected right left second first suffix
  | trans _ _ first second => exact .trans second first

private theorem fixed_consistent {classes : Constraints}
    (fixed : congruenceStep classes = some classes) : isContradicting classes = false := by
  dsimp only [congruenceStep] at fixed
  split at fixed
  · cases fixed
  · rename_i consistent
    have same := Option.some.inj fixed
    rw [same] at consistent
    exact Bool.eq_false_iff.mpr consistent

/-- If every completed class drops at a child, two paths through that child cannot have a common equal path. -/
theorem child_separate {classes : Constraints} (fixed : congruenceStep classes = some classes)
    (index : Nat)
    (dropped : ∀ paths ∈ classes, ∀ left right : Path,
      index :: left ∈ paths → index :: right ∈ paths → left = right)
    {left right other : Path} (first : Rel classes (index :: left) other)
    (second : Rel classes (index :: right) other) : left = right := by
  have sameChild := Rel.trans first (rel_symm second)
  rcases single fixed sameChild with same | ⟨paths, selected, a, aMember, b, bMember, suffix, firstSame, secondSame⟩
  · exact (List.cons.inj same).2
  have consistent := fixed_consistent fixed
  by_cases same : a = b
  · have pathsSame : index :: left = index :: right := firstSame.trans (same ▸ secondSame.symm)
    exact (List.cons.inj pathsSame).2
  have notPrefix := consistent_subsumption_irreflexive classes consistent paths selected
  cases a with
  | nil =>
    exact False.elim (notPrefix ⟨[], aMember, b, bMember, ⟨b, rfl⟩, same⟩)
  | cons firstIndex firstPath =>
    cases b with
    | nil =>
      exact False.elim (notPrefix ⟨[], bMember, firstIndex :: firstPath, aMember,
        ⟨firstIndex :: firstPath, rfl⟩, Ne.symm same⟩)
    | cons secondIndex secondPath =>
      have firstParts := List.cons.inj firstSame
      have secondParts := List.cons.inj secondSame
      have tails := dropped paths selected firstPath secondPath
        (by rw [firstParts.1]; exact aMember) (by rw [secondParts.1]; exact bMember)
      exact firstParts.2.trans ((congrArg (fun path => path ++ suffix) tails).trans secondParts.2.symm)

end MicroCFTA.SourceCurrentNormalizedChildSeparation

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNormalizedChildSeparation.Rel
#print MicroCFTA.SourceCurrentNormalizedChildSeparation.Rel
#print axioms MicroCFTA.SourceCurrentNormalizedChildSeparation.Rel

#check @MicroCFTA.SourceCurrentNormalizedChildSeparation.single
#print MicroCFTA.SourceCurrentNormalizedChildSeparation.single
#print axioms MicroCFTA.SourceCurrentNormalizedChildSeparation.single

#check @MicroCFTA.SourceCurrentNormalizedChildSeparation.child_separate
#print MicroCFTA.SourceCurrentNormalizedChildSeparation.child_separate
#print axioms MicroCFTA.SourceCurrentNormalizedChildSeparation.child_separate

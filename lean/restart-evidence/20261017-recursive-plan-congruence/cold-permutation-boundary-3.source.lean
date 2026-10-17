import MicroCFTA.SourceCurrentNormalizedPlanCongruence

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ColdPermutationBoundary
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open SourceCurrentNormalizedPlanRelation

private def first : Syntax Nat Bool := .node [.mk 0 false [], .mk 1 true []]
private def second : Syntax Nat Bool := .node [.mk 1 true [], .mk 0 false []]

/-- Separate cold heaps can attach different row payloads to the same returned node identity. -/
theorem independent_cold :
    Related first [] second [] ∧
    ∃ left leftAfter right rightAfter,
      build first [] empty = .done left leftAfter ∧
      build second [] empty = .done right rightAfter ∧
      left.referenceOf = right.referenceOf ∧ left ≠ right := by
  constructor
  · simp [first, second, Related, RowsRelated, RowRelated, ManyRelated]
  · simp only [first, second, build, buildEdges, buildMany, Outcome.bind, InternedNestedConstruction.work]
    refine ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩
    · decide
    · decide

#check @independent_cold
#print independent_cold
#print axioms independent_cold
end MicroCFTA.ColdPermutationBoundary

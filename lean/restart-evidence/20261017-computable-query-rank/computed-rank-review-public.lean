import MicroCFTA.IntersectNumericRank
import MicroCFTA.SourceRecursiveIntersectionComputedFuel

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

#print axioms MicroCFTA.IntersectNumericRank.combine
#check @MicroCFTA.IntersectNumericRank.combine

#print axioms MicroCFTA.IntersectNumericRank.combine_lt
#check @MicroCFTA.IntersectNumericRank.combine_lt

#print axioms MicroCFTA.IntersectNumericRank.combine_bound
#check @MicroCFTA.IntersectNumericRank.combine_bound

#print axioms MicroCFTA.IntersectNumericRank.rootSize
#check @MicroCFTA.IntersectNumericRank.rootSize

#print axioms MicroCFTA.IntersectNumericRank.rank
#check @MicroCFTA.IntersectNumericRank.rank

#print axioms MicroCFTA.IntersectNumericRank.ceiling
#check @MicroCFTA.IntersectNumericRank.ceiling

#print axioms MicroCFTA.IntersectNumericRank.parts_bound
#check @MicroCFTA.IntersectNumericRank.parts_bound

#print axioms MicroCFTA.IntersectNumericRank.rank_bound
#check @MicroCFTA.IntersectNumericRank.rank_bound

#print axioms MicroCFTA.IntersectNumericRank.root_decrease
#check @MicroCFTA.IntersectNumericRank.root_decrease

#print axioms MicroCFTA.IntersectNumericRank.local_decrease
#check @MicroCFTA.IntersectNumericRank.local_decrease

#print axioms MicroCFTA.SourceRecursiveIntersectionComputedFuel.ceiling
#check @MicroCFTA.SourceRecursiveIntersectionComputedFuel.ceiling

#print axioms MicroCFTA.SourceRecursiveIntersectionComputedFuel.ceiling_mono
#check @MicroCFTA.SourceRecursiveIntersectionComputedFuel.ceiling_mono

#print axioms MicroCFTA.SourceRecursiveIntersectionComputedFuel.schedule_numeric
#check @MicroCFTA.SourceRecursiveIntersectionComputedFuel.schedule_numeric

#print axioms MicroCFTA.SourceRecursiveIntersectionComputedFuel.initial_numeric
#check @MicroCFTA.SourceRecursiveIntersectionComputedFuel.initial_numeric

#print axioms MicroCFTA.SourceRecursiveIntersectionComputedFuel.initial_requiredFuel_le
#check @MicroCFTA.SourceRecursiveIntersectionComputedFuel.initial_requiredFuel_le

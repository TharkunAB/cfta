For this prose only, D(xs) means ∃edge∈xs, edgeMeaning holds ambient edge term, with one fixed ambient and term. No new public predicate is proposed.
A .cluster candidates keptReversed boundary denotes D(candidates ++ keptReversed.reverse).
A .scan pivot remaining incomparableReversed keptReversed boundary denotes D(pivot :: (remaining ++ incomparableReversed.reverse ++ keptReversed.reverse)).
The inner helper returns next/newKept/after as before, plus ∀ambient term, D(next ++ newKept.reverse) ↔ D(pivot :: (remaining ++ incomparableReversed.reverse ++ keptReversed.reverse)).
If common has candidate identity, H19 gives candidate⊆pivot. Removing candidate preserves this union because pivot stays present.
Otherwise, if common has pivot identity, H19 gives pivot⊆candidate. The actual next cluster is candidate :: (incomparableReversed.reverse ++ tail), with the SAME keptReversed.
Promotion removes pivot and keeps candidate. All earlier incomparable rows and the tail stay; the branch gives the same union language.
If neither test succeeds, remaining loses its head and incomparableReversed gains that head. List membership under append and reverse gives the same union without any semantic premise.
At empty remaining, H16 returns .cluster incomparableReversed.reverse (pivot :: keptReversed). Its denotation is the same union, although the list order differs.
At empty active candidates, H16 returns keptReversed.reverse. At a nonempty cluster, compose the inner boundary iff with the outer induction's kept-result iff.
The invariant is language equality under actual promotion/reversal. It is not Sublist, prefix equality, or a global pairwise-incomparability claim.

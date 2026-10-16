# Independent finite ordinary construction and initialization review

Reviewed on 2026-10-16. No material defect was found.
No source edit or Lake process was used for this review.

`FiniteOrdinaryConstruction.build/buildMany/buildEdges` recurse on actual source syntax.
Variables use the literal current environment lookup and missing-value Empty fallback.
Ordered child and edge loops transport the current environment's residency through each actual constructor return.
The result domain comes from the concrete makeEdge and makeNode readback laws at that returned heap.
Guards and equality classes have no restriction in the domain.
Mu and explicit union syntax are excluded from this intermediate construction domain.
`closed` denotes actual empty-environment construction. It does not promise syntactic absence of variable constructors.
It derives completed construction, domain, Facts, and residency without a supplied successful build.

`FiniteOrdinaryOuterInitial.stored` derives conditional native and merge laws from their empty tables and outer laws from fresh outer tables.
The theorem is structural only; physical Ready is supplied separately by actual construction history.
`constructed` uses covered actual field history, initial cache validity, and source domain to derive its own build and initial semantic Context.
It retains the caller's field interner.
The checked initialization then executes the actual empty-equality allocation on that retained interner.
It does not assert that the interner remains byte-identical after that allocation or that the Empty identity is zero.
`prepared` constructs the literal serial field preparation receipt first, then uses its actual history and final cache for construction.
No desired final Context, model validity, completed outer call, or future result law is a premise.
No Haskell global-cache reset or host allocation/demand schedule is asserted.

`initial-independent-review-kernels-1.log` passes with exit 0 and no warnings.
It contains two named proofs, two axiom checks, and two signature checks.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. No `sorryAx` occurs.
The first proof constructs a two-level generic ordinary syntax tree with arbitrary full guards.
The second starts from the literal preparation result and derives actual Context, all three structural certificates, input domain,
the exact returned constructor heap, actual empty-interner growth, and inherited readiness at the computed canonical identity.
General outer graph existence and reached machine bounds remain separate obligations.

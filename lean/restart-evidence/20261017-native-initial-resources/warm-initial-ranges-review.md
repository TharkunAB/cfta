# Initial numeric ranges at a warm checked entry

Reviewed: 2026-10-17 05:07 CEST.

The new `warm_initial_ranges` endpoint accepts the full current checked state. It does not initialize or replace its native tables or equality operations. It derives checked `WordRanges` and enter-key `Prefixes` from `Good`, `SemanticReady`, original available operands, and three initial numeric inequalities. It requires no idle condition, result, completed trace, or future range plan.

The query-entry heap is the immutable source. Its actual node counter is less than `2^bits`. Its actual row counter is at most `2^(bits+2)`. Domain headroom covers the complete source inventory of length `2^(N+N*N)`, where `N` is that entry heap's node counter. The existing strong raw-prefix admission proof retains source operand identities and exact domain allocation history. It does not require newly constructed output identities to become source operands.

This preserves the existing general recursive family. It permits positive constrained ordinary prefixes, hereditary Mu atoms, explicit source unions, and scoped references under the existing original-input contract. It does not restrict the request to finite ordinary syntax or hereditary operands alone.

The source inventory is conservative and can make the hypothesis impractical at a fixed host width. The theorem does not improve that bound or prove later queries have enough initial headroom. It also does not derive semantic correctness for arbitrary warm memo results. Such a result requires the separate causal contextual and joint returned-cell laws. Range admission alone imposes no returned-result law.

The imported integration kernel applies the endpoint to an arbitrary actual raw prefix from the same warm entry. It derives the reached word checks, suffix word ranges, exact domain-allocation trace, and strict bound on the actual returned domain counter. The supplied prefix is used for preservation only. The production endpoint derives the universal range predicate without it.

Strict production passed on attempt 1 with a zero-byte log. Canonical compilation passed in the 1246-job combined build. The only warning is the historical dependency warning at `InternedFreshOrdinaryClosedCompletion.lean:24`. One imported public axiom/full-signature pair and one integration pair passed with no diagnostics, `sorryAx`, or truncation.

The generic native compiler and current checked edge body have different branch and allocation behavior. This endpoint certifies the current checked raw prefixes. It does not transfer those prefixes to the generic executor. The previously proved cold checked `RecursiveInitialRanges.initial_ranges` and `cold_complete` remain unchanged.

# Constructor observation boundary

The selected runs are `writer-boundary-filter-2` and `writer-boundary-smart-3`.
Each run checks one source-built theorem with its full signature and axioms.
The package has no new production module. It does not need a canonical target.
The printer-free strict run checks the same two proof bodies together.

## Actual self filtering

`WriterFilterBoundary.actual_filter_boundary` constructs one source node.
Its children contain A(a), B(a), closed raw Mu(empty), and open raw Mu(a).
A and B have symbols 0 and 1. Their raw guards are false and true.
Each ordinary row has the one ordered child a.
The source argument a is the available reference `uninterned 0`.
AB is the actual `makeUnion [A,B]` result.
M is the source-built closed raw Mu(empty). N is the source-built open raw Mu(a).

The actual union inputs are x = union[a,A,B,M] and y = union[N,AB,M].
The theorem proves the exact production `Survival.Related x y`.
Both values are physically nonempty. Both roots are not bare references.
Their full `free` lists, `deepNames` lists, and cached depths are equal.
All finite observations agree in every fixed view.
The two actual sequential `withoutSelfReference a` calls fail `Same 0`.
The first call removes the literal bare a member. The second call retains N.
N still exposes a when the observer unfolds it.

This is a counterexample to self-filter congruence from Related alone.
The equal aggregate lists and depth do not repair that proposed rule.
The test that the whole root is a bare reference also does not repair it.
A useful next relation must retain the literal immediate alternatives that
self filtering tests, or prove the required filter result by an actual source law.

## Actual smart source builds

`WriterSmartBoundary.actual_smart_boundary` starts with an empty source cache.
The first source is `binder true (union [binder false empty, var 0])`.
It returns the actual closed raw Mu(empty), with its full reached Ready heap H.
Its warm replay at H returns the same value and the same full heap H.
The second source is `binder true (var 0)`. Its actual call starts at H.
It returns Empty. The theorem retains the actual full result heap and Keeps.

At H, for every AVAILABLE reference r, both raw body builds complete.
Their actual results satisfy the exact production Related relation.
The smart results still agree on every finite observation in every view.
They fail Related because raw Mu(empty) is physically nonempty and Empty is empty.
The raw-body premise is checked at H only. It is not quantified over all future
callback heaps. This example does not refute a stronger rule with that premise.

## Remaining writer obligation

Neither theorem is a counterexample to the selected SAME-writer body/ordinary
reconstruction relation. That general statement remains open.
The existing closed raw Mu boundary is retained in the source pins.
It shows why all-depth observations alone cannot imply physical emptiness.
Smart finish also tests own-name free membership and bare-self identity.
A relation for that operation must derive those tests at the actual selected
writer, in addition to immediate root filtering and ordered child observations.
These are proof boundaries. They are not Haskell defects or nontermination claims.

## Validation and failed attempts

The final probes have all eight explicit options, `#check @`, and axiom prints.
Their logs contain no diagnostics, omitted terms, or `sorryAx`.
Only the three standard axioms are permitted by the verifier.
Every attempt ran its own immutable numbered source under Lean 4.34.1.
The effective memory limits are max=4 GiB, high=4 GiB, and swap=0.
Filter attempt 1 and smart attempt 1 failed. Their exact sources and logs remain.
Smart attempt 2 passed before the common-start warm replay was added in attempt 3.
No old proof, frozen evidence, Haskell source, or production file was edited.

# Sound decided acceptance

`MicroCFTA/AcceptanceSoundness.lean` connects the actual three-way search to
independent semantic runs. A semantic guard is a proposition. It need not be
decidable. A stable callback supplies Yes, No, or Unknown.

`yes_sound` proves that a Yes result supplies a semantic accepting run when
callback Yes results are sound. `no_sound` proves that No excludes every
semantic accepting run when callback No results are sound. Neither theorem
requires a decision for every guard. `accepts_supports` combines the two
results with `Guards.Supports`. Unknown supplies no semantic evidence.

The No proof uses a cache invariant. A stored false result refutes its
registered subtree whenever the global Unknown flag is false. The proof
establishes this invariant for an empty table and every insertion. A hit
uses the stored refutation. A miss proves a new refutation before insertion.

`allM_checked` carries a failed child's refutation through the child loop.
`anyM_checked` combines the rejected alternatives. The latter uses the
proved call-list prefix relation and tracked global flag to recover that
earlier alternatives also completed without Unknown. Thus a cached false
caused by Unknown cannot become a semantic refutation merely because a
later cache hit skips the callback.

`shared_checked` proves the complete shared worker invariant.
`unshared_checked` proves the adaptive caller. It covers no matching edge,
one matching edge, and fresh shared cache allocation. A local shared cache
can be discarded, but its Unknown effect persists. Numbered subtree
registration and structural height establish the cache and recursion
premises for the public entry point.

The semantic contract is explicit: a callback Yes implies its guard's
meaning, and callback No refutes that meaning. These are solver obligations.
The proof derives search soundness from that contract. It does not assert
SMT soundness, termination of external solver calls, or stability of an
arbitrary effectful callback. It does not require guard completeness or
replace Unknown with false in the semantic language.

Validation: `lake build MicroCFTA.AcceptanceSoundness` succeeds with the
pinned Lean toolchain. The module contains no proof placeholders.

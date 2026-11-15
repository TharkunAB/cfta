# Actual checked edge query Returned preservation

Status: UNCOMPILED candidate. No proof credit is claimed.

The candidate proves preservation of both existing `Returned` predicates at
every supplied-fuel endpoint of `.code (.edge request .pure)`. The body is the
actual `.edgeBody` control. It retains field lookup and equality allocation.

The inputs retain physical cache validity, actual `EdgeReady`, original edge
`KeySafe`, and both incoming `Returned` laws. The local body induction
hypothesis applies only at a literal `Steps 1` prefix of this same query. It
retains the exact original request and its actual continuation. Its budget is
strictly below the original supplied query fuel. This is proof infrastructure
for a mutual execution induction. It is not a new original caller contract.

Publication and demand preserve the prior returned laws. Physical exactness
identifies the started request with the original request. The actual clean
body trace retains the evaluating edge cell through
`SourceEqualityNativeDemandRunning.trace_retains`. The existing
`returned_finish` rule then stores the same literal producer row. The proof
does not assume a future running cell, a resident output row or a model.

Zero fuel, absent and busy demand, ready hits, partial bodies, field blocks,
constraint errors, failures and completed body/finish prefixes remain covered.
Only an actual trace to the pure body value can trigger the publication case.

This theorem preserves supplied predicates. It does not establish a particular
semantic predicate for all producer bodies. It does not prove a full
initialized execution invariant or the one-assignment source completion goal.

The public node-query theorem was inspected before this candidate was written.
No existing actual edge-query Returned theorem was found by the recorded
search. Existing physical, clean-trace and returned lifecycle lemmas are used.
No cache framework is added.

No compiler, live source edit, Git action, board action or `/tmp` action ran.
No Haskell source changed. No Haskell bug or fix is claimed.

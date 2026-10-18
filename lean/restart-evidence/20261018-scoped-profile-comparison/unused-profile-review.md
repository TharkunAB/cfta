# Unused smart Mu profile reduction

Reviewed and checked on 2026-10-18. The new module has one public theorem, `smart_unused`. It does not assume an actual execute equation, a fresh marker, a complete publication law, or any desired output relation.

The theorem accepts an available stored Mu in a coherent heap. It also accepts the existing probe-depth Correct predicate, the new parametric ProfileContract.Correct predicate, and the actual `usesLocal = false` branch. For every outer profile assignment, it compares the denotation of the smart return with the ordinary probe denotation whose own local is assigned the Empty profile.

The proof follows all three cleanup cases. If own is absent from body.free, cleanup returns the body. The free-support congruence theorem permits the Empty local override there. If the body is bare own, cleanup returns Empty. Reference denotation supplies the same Empty profile. Otherwise cleanup would retain Mu. The raw and smart probe-depth equalities would then force `depth + 1 = depth`, which is impossible.

The new parametric Correct predicate is an explicit assumption. This module does not derive it for arbitrary publications or arbitrary resident caches. Its conclusion compares root profiles. It does not prove equality of complete values, full rows, or finite observations.

The source-built integration executes two closed initial source calls from the empty heap. One is `.binder true (.var 0)`. Its stored body is bare own and its result is Empty. The other is `.binder true (.node [.mk 7 false []])`. Its unused body is a nonempty ordinary node. The fixture derives both Ready heaps, exact stored candidates, availability, probe-depth Correct, unused flags, and the new parametric Correct predicate. It invokes `smart_unused` for every outer assignment. No future receipt or supplied heap invariant appears in the constructed statement.

Validation: production direct1 has a zero-byte log; canonical1 completed without a warning; public1 prints the one complete public statement, proof, and axiom set. Constructed kernels2 has a zero-byte log. Kernels-public1 prints its complete public statement, alias proof, and axioms. Both full groups use all eight print options and only the standard permitted axioms. Every job verified memory.max = memory.high = 4294967296 and memory.swap.max = 0 under a five-minute cap. The first fixture attempt is retained. It had two local proof errors: an omitted concrete body/probe equality and an unfinished nonempty-list negation. It did not expose a production defect.

# Full source observations permit arbitrary literal aliases

`InternedLiteralObservations.build_empty` and `callback_empty` compare
actual complete full-syntax executions. Literal lexical inputs of equal
length give the same EmptyNode decision. The inputs can contain arbitrary
aliases. The theorem requires the constructor invariants at each actual
starting prefix. Closed source execution derives those invariants.

`callback_self_forward` and `build_self_forward` cover both normalized
callbacks and raw body execution. If the first supplied local is absent
from its captures and the first result is exactly that local, the target
result is its supplied local. The target local can equal a captured name.
There is no injective-name-map premise and no assumed callback relation.

The proofs use the full source profile theorem. A direct fresh-local result
forces the symbolic body to have no captured root reference and to use its
argument. The constant-name map preserves and reflects this class under
all equal-length literal input lists.

These observations supply the empty and bare-local parts of paired source
execution. Exact identity under boundary absence still needs the dynamic
recursive-request argument. The observations do not prove that argument.

Exact ordered root-profile correspondence is too strong. A temporary
kernel-checked fixture executes two smart binders under `[Depth, U0]`.
The first body returns its captured variables in their original order.
The second returns them in reverse order. Both request the Mu key
`(U0, Depth)`. The second call returns the first complete representative,
whose root profile is `[Depth, U0]`. The pure interpreter for the second
body returns `[U0, Depth]`. The existing set-based `Equivalent` theorem
holds. Exact list equality does not hold. Both actual calls complete.
This is a proof boundary, not a source termination counterexample.

The focused build completes 240 jobs with Lean 4.34.1. The isolated audit
checks 8,841 theorem dependencies. Both checks pass. No Haskell source
changed for this proof.

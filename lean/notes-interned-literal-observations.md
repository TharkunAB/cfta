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

`InternedFreeAbsenceReplay.build_related` now proves full raw source replay
when one changed interned name is absent from the first result's free set.
Both compared calls must have completed in a common coherent cache. The
recursive case reads absence from both actual request probes. It then
compares the smaller source bodies and reuses the canonical request.

`InternedFreshCallbackBoundary.callback_clear_of_raw_absent` transports
boundary absence from an actual fresh callback to an actual sentinel
callback when the raw fresh body omits its local. It permits target aliases.
It does not require equality of the two filtered callback results. The case
where the fresh filter deletes a root local from a union remains separate.

`InternedLiveInputReplay.build_same` compares several changed lexical inputs
at once. Abstract atoms identify the input positions before actual reference
aliases occur. The pure free-name interpreter selects the live atoms. Only
those atoms must have equal references. The full mutual proof also compares
ordered child results and surviving edge records. The binder step compares
both actual normalized probes and then reuses the complete request.

`InternedLiveInputReadiness.not_pending_after_probes` uses an earlier completed
binder and the later call's two completed probes. Agreement on live inputs
excludes the later missing-record condition. It does not assume that the
later binder completes. `InternedLiveInputSupport.not_pending_of_fresh_changes`
derives that agreement when every different lexical input is a fresh interned
name and the later depth probe was already available before those names.

General pending-site exclusion remains open. An earlier completed trace must
supply the corresponding site with agreement on its live inputs. Choosing
Depth at every crossed binder can change a live ordinary-probe local.
Matching the callback choices must also account for their computed ordinary
levels. The old final probe alone does not show that all crossed locals are
absent. No theorem here assumes equal ordered profiles or equality between
a stored body and either one of its probes.

Pinned Lean 4.34.1 builds the live-input support target in 265 jobs. The
isolated checks for full live-input replay and pending-readback exclusion
use only `propext`, `Classical.choice`, and `Quot.sound`. These modules
change no Haskell source.

Status: UNCOMPILED complete source-only draft. No theorem credit.

The module preserves all four private helper and consumer declarations from
115250. It adds one import, one private whole-prefix replay law, and the exact
original public resource target with a complete proposed body. The frozen
115250 packet is unchanged. target-header.lean.txt is byte-identical to it.

The new replay proof tests the actual read and check observations. A missing
pending singleton stops. A check with neither supported Bool singleton stops.
A repeated check with no parked adapter is exempt. A successful parked adapter
replays exactly. A false check derives the actual entered Frame, then applies
the public identity pending law at both bounds. Deterministic lookup equates
the two decoded values. Empty and nonempty cases preserve the whole result.

These local existence cases are proof case analyses on actual deterministic
operations. They are not new theorem hypotheses or input providers. The final
resource header adds no read, check, successful adapter, or replay supplier.
It preserves the same caller and full Memos. Failure branches stay explicit.
The actual no-output consumer equation remains in the same module.

The final proof obtains the existing sufficient common bound, compares fuel
to fuel+bound, aligns bound+fuel by addition commutativity, and transfers the
resource predicate only along the whole-result equality. No safety claim is
inferred from eventual completion alone.

Root must check all four old helper bodies as well as the new bodies. The raw
unsupported cases use Lean split on the actual operational match. The branch
hypotheses should supply exact observation equations to the existential
contradictions. These tactic scripts have not been checked here.

No compilers, live sources, Haskell, Git, or board actions. No objects, cache,
or build artifacts are included. The global finite-witness, generated-type
closure, outer whole-CPS, and Haskell correspondence gaps remain outside scope.
No Haskell fix was identified.

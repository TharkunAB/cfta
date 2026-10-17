# Actual warm union selection

The public `warm` theorem takes an actual makeUnion return and an actual
warm stored reconstruction at one common heap. Its selected inputs are
exactly `distinctNodes (originalInputs.flatMap unionMembers)`. Actual warm
calls of these selected values give the comparison result list. The theorem
proves the same finite open observations at every depth and every fixed view.
It does not require a flattening fixed point.

The empty and singleton cases retain the literal constructor return. The
ordinary case derives atomic flattening and physical identity uniqueness
from the actual selection. It then uses the actual ordinary-row expansion
theorem. The remaining case reads the complete union payload from the actual
nodeStep result. Coherence fixes its members and metadata. Initial ready
reconstruction constructs its original member calls. Literal execution
determinism and exact common-heap replay align these calls with the supplied
actual warm observations. No desired member-result law is assumed.

The theorem requires Ready at the common heap, availability of the selected
values, and available replacement values. It allows open stored unions and
arbitrary nested Mu children. The generic theorem is conditional on actual
warm call observations. It does not construct both initial operation orders.
The separate root StoredUnionFusion module owns that initial composition.
The conclusion concerns observations at one fixed view. It does not assert
physical Value equality or cross-view transport.

The final source is byte-identical to strict attempt 3. Its strict log is
empty. Canonical attempt 1 passes. Public attempt 1 checks the one public
declaration with all eight printer settings and standard axiom output.
Constructed attempt 1 has one no-premise source-built case. The original
source union contains a productive raw Mu, an open ordinary reference, and
an ordinary node. It constructs three ordered member calls, derives exact
same-heap makeUnion and repaired-execute replays at their returned common
heap, and applies the new theorem. It supplies no future completion or heap
invariant. The final public and constructed logs have no diagnostics.

All selected runs use Lean 4.34.1. The worker reads actual memory.max and
memory.high as 4 GiB and memory.swap.max as zero. Failed strict attempts 1
and 2 remain intact. They exposed a local name collision and an incorrect
namespace for the existing distinctNodes uniqueness lemma. No older source
or frozen evidence file changed.

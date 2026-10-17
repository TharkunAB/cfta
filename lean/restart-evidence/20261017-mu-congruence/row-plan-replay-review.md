# Row plan replay review

The module has four public declarations. `rowRun` evaluates the literal
ordered child plans and then calls `makeEdge` with the literal symbol and
full guard. `equivalent` proves all-outcome equality at any current heap
for equal fields and `ManyEquivalent` child plans under two capture lists.
It needs no cache validity or completion premise.

`replays` derives exact row replay from the repaired child-list replay and
the actual finite edge Work replay. Its private growth helper uses the
actual child prefix and Work return. Arbitrary nested binders and unions
remain allowed. No Prepared or semantic restriction is added.

`rows` consumes one actual completed `buildEdges` equation, initial cache
validity, and growth from its final heap to the common heap. It derives an
ordered `Language.All₂` between every original row plan and returned edge.
Each relation is an exact `rowRun` return at the same common heap with no
further effects. The proof splits the actual first row and suffix. Actual
prefix validity and suffix growth supply the replay premises. No caller
supplies separate per-row results or future completion laws.

The no-premise integration builds two rows. One row contains a captured
nested raw Mu. A later fresh edge allocation strictly increases the edge
counter. The integration derives every original row's exact common-heap
replay. It also derives the first return under recoded lexical slots and
a different capture list, using the public equivalent-plan theorem.

Selected strict3 is empty. Canonical1 passes 152 jobs. Public1 covers all
four full signature/proof/axiom pairs. Kernels2 covers one constructed pair.
All eight printer settings are explicit. Selected proofs use only propext
and Quot.sound. All jobs record 4GiB memory.max, 4GiB memory.high, and zero
swap. Failed strict1/2 and kernels1 are preserved with exact raw snapshots
and logs. The owned peaks file snapshots the shared append-only peaks file;
the manifest does not pin that mutable shared path.

The main theorem verifies a completed row-list observation. It is not an
initial completion theorem for an arbitrary source plan. It proves no
cross-view observation transport and no equality between Mu reconstructions.

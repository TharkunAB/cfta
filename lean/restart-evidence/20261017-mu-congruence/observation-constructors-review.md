# Common-view constructor review

The module has five public theorems. `seeds` composes an ordered `All₂` of
singleton observations. `node` matches literal ordinary rows by occurrence.
Each row keeps its complete symbol and guard. Its children match in order.
Neither theorem requires a shape restriction on Mu children.

`makeNode` compares the exact results of two literal constructor calls.
Each initial state supplies `Facts` and residency for its input rows.
The caller matches their surviving row occurrences in both directions.
Canonical sorting and identity deduplication need no injective row mapping.
The theorem derives output row origins and absence of exposed references
from actual canonical readback. It assumes no desired output relation.

`makeUnion_normalize` proves that an actual normalized union has the same
observations as its original seed list. The proof derives reference-origin
normalization separately from complete row-origin normalization. Facts and
available input records justify flattening and identity deduplication.
The live heap justifies the ordinary row merge. `makeUnion` composes two
actual calls through the ordered seed relation in one common view.

The states used for the constructor calls can differ. The observation view
is one explicit common heap. These theorems do not transport observations
between views. They impose no Prepared, closure, finite-cap, or noDeep
restriction. They assume no future completion. Mu children occur only under
the supplied smaller-depth relation, or the exact physical origin proofs.

The first no-premise integration constructs a productive raw Mu. It builds
open rows with the Mu and a Depth reference. Duplicate and reordered rows
produce related actual node calls. The test checks the exact false guard.
An actual union with duplicate Mu, Empty, and Depth operands retains both
finite observations and the exposed Depth reference.

The second no-premise integration proves the normalization boundary.
Empty and an actual nonempty ordinary leaf satisfy `Same 0`. Their actual
parent constructors do not satisfy `Same 1`: the Empty child deletes its
row. Thus bare child observations cannot discharge node survival alignment.
This is not a counterexample to the theorem with its survival premise.

Selected strict2 is empty. Canonical1 passes 561 jobs. Public1 checks all
five full signature/proof/axiom pairs. Kernels2 checks both integrations.
All eight printer settings are explicit. The selected proofs use only the
standard axioms. Each job records 4GiB memory.max, 4GiB memory.high, and zero
swap. Failed strict1 and kernels1 remain unchanged with their raw logs.
The owned peaks file snapshots the shared append-only peaks path. The
manifest does not freeze that mutable shared path.

This component proves actual constructor congruence in one view. It does
not prove the nested-Mu fusion or a change-of-view theorem.

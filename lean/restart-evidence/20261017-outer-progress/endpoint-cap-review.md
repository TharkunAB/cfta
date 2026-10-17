# Finite caps at actual primary endpoints

Checked on 2026-10-17 at 16:17 CEST. Production source
`SourceCurrentPrimaryEndpointCap.lean` is frozen at
`e18c58d403a5ef1c2b6abc93b4647562ac2436667c73ef1e1ffec51f65c69f17`.

`reaches_cap` takes an initial coherent heap, an available value, and its
actual source endpoint descendant test equal to false. It derives
`Cap Plain (InternedValueMass.value value) value`. It assumes no input Cap,
closedness, completed worker, future resource bound, or desired output law.
`reaches_finite` supplies the resulting finite depth witness.

The proof follows actual available children. For an ordinary node or union,
Coherent.NodeFields identifies the cached depth with the maximum child depth.
If the source skips a zero-depth parent, every child also has zero depth.
Otherwise its actual witness traversal excludes a constrained Mu in each
child. Member mass bounds raise each derived child cap to one common bound.
A Mu reads its actual source predicate. GatePlainRegion.annotations then
derives its hereditary Plain condition and Cap zero. Both stored probes are
included in the quantitative payload mass, but not in the annotation traversal.

`endpoint_clear` derives the descendant exclusion from an actual false
PRIMARY NodeTrace at the empty endpoint path. `endpoint_cap` applies the
initial producer to that same original endpoint value and physical heap.
These are actual-trace adapters. They do not construct a full selected path
query or claim cap retention through later Required or class edits.

The PRIMARY restriction is essential. The current secondary policy permits
a closed constrained Mu exactly at the endpoint. Such a Mu can lie outside
every finite Cap. A false secondary endpoint cannot replace this hypothesis.
The isolated descendant predicate also returns false on references. The
primary endpoint trace retains its separate reference and union refusals.

The final integration constructs its own ordinary equality-bearing value
from empty. Two productive plain Mu children give cached depth one. Its own
guard makes the value nonhereditary. The proof derives SemanticReady,
availability, closure, the actual false primary trace, Cap at its payload
mass, and the failure of Cap zero. A distinct-path class `[[0],[1]]` on
`[value,value,depth-reference]` returns the actual false primary answer.
The unselected open reference is available. No all-forest closure is assumed.

Direct attempts 1 and 2 retain their raw failures. Attempt 3 is empty under
all linters. Attempts 1 and 2 were first written in the previous evidence
directory by mistake. Their four new artifacts were moved intact into this
directory. Their logs retain the original absolute diagnostic paths. No
previous frozen artifact changed. Canonical attempts 1 and 2 failed before
building because the user bus was unavailable in the environment or sandbox.
Attempt 3 passed 1087 jobs with effective MemoryMax and MemoryHigh of 4 GiB,
zero swap, and recorded peak 206 MiB. It replays only the inherited unused
`inputs` warning. The four public probes print signatures, proofs, and axioms.
Only final integration attempt 5 counts. It prints its signature and axioms.
All final checks use only the standard Lean axioms.

This component derives a selected-endpoint property from current policy.
It does not restore a whole-forest Cap premise. It does not establish a
decreasing outer rank, busy exclusion for general live descendants, or
general outer completion. Origin and path transport across parent edits
remain separate proof obligations.

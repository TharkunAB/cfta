# Retained Mu reconstruction and actual writer growth

Proof checkpoint is `7a441d2d`. Source main is `c0cc8a05`, merged locally at `896b0a1c`.
The whole-library target and remaining areas are in
notes-proof-status-20261017.md. This checkpoint is progress toward that
target. It does not complete retained-Mu reconstruction congruence.

## Actual reconstruction

SourceCurrentStoredReconstruction.execute constructs complete repaired
substitution from initial Ready, source availability, and replacement
availability. The result retains Ready, cache growth, issued-reference
history, output availability, and a local causal publication history.
Arbitrary nested Mu records are allowed.

Its mu theorem reads both payloads from the selected cached Mu. It derives
their availability from that record. It constructs two sequential calls.
The first substitutes the selected identity in the stored body. The second
substitutes the ordinary probe name in the stored ordinary value. Both use
the same available replacement. The theorem retains both actual results,
the intermediate heap, both local histories, and the original selected Mu.
It does not compare the two returned values.

SourceCurrentStoredReconstructionReplay.mu starts with the same inputs and
an initial causal history from empty tables. It extends that history through
both calls and derives the original writer. Both exact calls replay with
their own results at the common final heap. Neither replay changes that
heap. This is not equality of the two reconstruction results.

## Actual writer growth

SourceCurrentNativeMuGrowthHistory.Path strengthens publication history.
Every retained step supplies both NoNewMu and actual Grows. Publication
retains all three callback paths. Path.history preserves the earlier causal
history contract. Path.growth derives growth of all four cache tables.
NoNewMu alone does not imply growth. Four-table Grows does not imply
issued-reference extension. Obtain that history separately when required.

SourceCurrentNativeMuGrowthExecution constructs these paths from actual
source execution and the initial joint context. It covers expressions,
ordered children, and ordered rows at every stopping outcome. Each Work
step derives growth from its own returned state. The source caller supplies
no future successful return or future growth law. Closed source construction
starts its path at the actual empty tables.

SourceCurrentNativeMuGrowthWriters follows the selected first writer through
those paths. A final record either was present initially or has a literal
publication with all earlier callback paths. The publication's final heap
grows into the reader's heap. Empty initial tables eliminate the first case.
Both raw ordinary and reserved-body callback heaps therefore grow into one
actual reader heap. This includes records selected through later warm hits
and candidates discarded by keep-first publication.

The connected integration builds a nested raw Mu from empty tables. It
constructs both reconstruction calls and their common final replays. It
also carries the selected writer's actual heap into that common final heap.
It does not assume growth from a bare History.retain constructor.

## Open observations

SourceCurrentOpenObservations.Same compares seed lists in one fixed epsilon
view. Depth zero retains exposed bare-reference names. Each additional
depth retains row occurrences with exact symbols and full guards. Children
are related in their original order. Normalized rows can be removed or
reordered, so the relation does not assert equal row counts or positions.

The relation is reflexive, symmetric, transitive, and closed under lowering
the depth. Actual Mu unfolding preserves it at every depth in the exact
entry view. Initial semantic heaps, payload coverage, and availability
construct that unfolding. The result includes the actual returned heap and
its semantic facts. Transport to a different view still requires a separate
replay argument.

A checked boundary shows why bare references are necessary. A bare Depth
reference and Empty have the same constructor row origins. They have
different depth-zero open observations. Row-only origin equivalence is
therefore insufficient for a substitution congruence proof.

## Remaining proof

The next main producer must relate the two actual reconstructed results,
or establish their full open observations and ordered child provenance.
It must handle retained-used Mu through causal first-writer history.
The current plan-equivalence law compares one original stored value under
different capture layouts. It does not compare distinct raw callback values.
The unused-Mu law does not supply the retained-used branch.

Freshness must concern live fixed captures. The actual ordinary probe and
reserved identity have freshness producers. The Depth marker can alias an
outer capture. Do not treat it as a fresh marker without a lexical argument.
Do not replace this obligation with Prepared, global closure, a supplied
result relation, or an assumed future completion.

The finite exploration covers forty completed trials. Thirty select a used
local binder. They cover raw unused inner Mu, nested used Mu, an open selected
inner Mu, and ten available replacements. All returned identities match,
and the second call allocates no node. Two independent kernel proofs show
full Value equality with actual source construction, initial readiness,
available replacements, retained selected records, causal histories, and
common-final replays. One replacement aliases an outer captured name.
These finite results do not prove the general reconstruction equality.

General recursive outer-node progress, nonempty live walks, full mutual
completion, repeated-pass convergence, current frontend/error adapters,
concrete runtime effects, and public Haskell composition remain open.

## Validation and Haskell handoff

The full pinned Audit and final source checks are recorded in
restart-evidence/20261017-retained-mu-reconstruction/. Read its README and
checkpoint-validation.json for exact counts, caps, and frozen hashes.
Earlier proofs, repairs, counterexamples, drafts, and evidence are retained.

No Haskell behavior patch or new production defect is added. The documented
smart cleanup in cfta/src/Data/CFTA/Interned/Type.hs explains the earlier
physical rebinding boundary. FINDINGS.md retains the external repair
registry first. Field-pool repair b9219b9e is merged and validated. It rejects
the invalid recursive field-pool derivation with FieldAtomOnDatatype.
Standalone holds retains its opaque-pool evaluation. The unchanged Haskell
source retains the strict Nix all-component build, 798 examples plus golden,
Fourmolu, and Cabal-gild validation from the earlier source refresh.

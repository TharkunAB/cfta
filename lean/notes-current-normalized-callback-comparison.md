# Current normalized callback comparison

Updated: 2026-10-17 19:31 CEST. Proof checkpoint is `179b5a09`.
Starting checkpoint is `87a430e2`. Source main remains `c0cc8a05`,
merged locally at `896b0a1c`. The complete library proof remains open.

## Actual source publication

`SourceCurrentNativeMuPublication.build_history` derives a finite history
at every actual source stopping state. Each publication retains the Depth,
ordinary, and reserved-body callback histories as strict subtrees. It also
retains the source body, captures, exact states, and missing-key reservation.

`History.writers` follows literal keep-first selection. A writer has an
empty record slot immediately before its publication. A discarded later
candidate cannot serve as that writer. `closed_writer` derives the writer
from a closed source execution. `closed_warm` retains the writer and the
complete unchanged state of an actual warm return.

`SourceCurrentNativeRequestWinner.winner` recovers the literal selected
record after any successful request. It assumes no callback result law.
`SourceCurrentNativeRequestProbes.request_probes` uses physical cache facts
and probe availability at that returned heap. It derives equality of the
complete stored and requested probes. Key equality alone is insufficient.

`SourceCurrentNativeMuPublicationCallbacks.raw_callbacks` decomposes the
actual ordinary and body callbacks into source builds and exact filters.
Its state facts follow from those actual executions.

These histories establish publication order. Reservation identities do
not give that order. An outer reservation can precede an inner publication.
The history does not itself prove the normalized body-to-ordinary law.

## Full lexical support and root normalization

`SourceCurrentNativeNormalizationFreshness.ordinary` derives freshness
against all live instantiated support, including varying lexical slots.
It uses the actual completed Depth callback. Varying slots can share a
reference. A discarded fixed capture can contain the chosen ordinary name.
`reserved` derives freshness from the actual missing-key reservation.

`SourceCurrentNativeStrippedAlternatives.union_stripped` gives the exact
ordered root alternatives after selected references are removed. A retained
bare reference rules out ordinary-row merging. Duplicate names are allowed
in the list of removed references. `SourceCurrentNativeStrippedFilter.filter`
extends this equation through the actual own-reference filter when a
distinct outer reference survives.

`SourceCurrentNativeLocalRecordErasure` weakens record replay to normality
of the selected value. The whole heap need not have irreducible unions.
`root_reference` derives the local premise from a bare root reference.
`same` compares actual erased records in a common later heap. Equality of
the ordered stripped alternatives remains an input to this theorem.

## Full outer invariant transport

`SourceCurrentUnionNormalOuter` retains UnionNormal through all eight
mutually recursive bounded outer workers. It covers node and edge calls,
their bodies, ordered rows, descendants, children, and indexed walks.
Only the initial invariant and the actual worker arguments are required.
The theorem includes every stopping outcome. It assumes no later callback
preservation law. It does not prove successful outer completion.

Two constructed integrations run actual full outer node calls. They cover
an unrelated active node owner, exact zero-fuel ready hits, a constrained
ordinary value beside a productive Mu, and later Required execution at the
actual returned heap. They do not establish general progress.

## Complete source comparison and causal readback

`SourceCurrentNativeNormalizedComparisonExecution.history_unused` derives
unused smart readback for every retained Mu in an actual publication
history from empty tables. `closed_unused` constructs that history from
closed source execution. If the actual probes report no deep local use,
smart cleanup equals bare-self erasure of the exact stored ordinary probe.
The probe uses the actual repaired ordinaryLevel selected from Depth.
The theorem retains an earlier winning payload on a warm request.

`closed_compared` compares arbitrary nested source syntax with fixed
captured records and a finite set of varying lexical slots. It derives
the internal stored law from a common heap built by actual closed source
construction. The caller supplies both actual completed raw calls, their
entry Context and DepthHeap, and growth and issued history into that heap.
Both assignments must be fresh against live fixed support. The first
result has no deep assigned name. The conclusion identifies the ordered
root alternatives after the assigned names are stripped. It permits
aliases and discarded captures that contain the chosen ordinary name.
It does not claim literal equality of the raw records.

The private syntax induction uses the internal immutable Mu law only at
the common final heap. The history induction then proves that law. It
processes Depth, ordinary, reservation, and body before candidate
publication. The body history already establishes the law needed for the
smaller source comparison. `Candidate.candidate` derives the new payload
law before keep-first completion. No desired Heap law is a public input.
NoNewMu itself supplies neither growth nor semantic cache facts.

## Remaining work

Compose these source results with actual recursive native callback and
row histories. General outer-node progress, repeated-pass convergence,
current frontend and runtime adapters, and full public composition remain
open. One normalized source comparison is not a whole-library theorem.

The comparison needs freshness of both varying assignments against live
fixed support. Freshness of only the second assignment proves the narrower
deep-name absence transport result. It does not prove stripped equality.
Read `notes-proof-status-20261017.md` for the whole-library target.

## Haskell handoff

No Haskell behavior patch or new production defect is added. Root FINDINGS
keeps the repair registry first. Field-pool repair `b9219b9e` is already
merged and validated. The Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pools.
The unchanged source reuses its strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild checks.

## Verification

All 17 final strict source logs are empty. All canonical targets pass.
The full pinned Audit passes 3080 jobs and 67877 dependency checks.
Actual limits are 4 GiB MemoryMax, 4 GiB MemoryHigh, zero swap, and
399 MiB peak memory. Only standard kernel axioms are permitted.
Read the evidence README and checkpoint-validation.json for final selected
public and constructed probe counts. Failed attempts retain their exact
executed snapshots and raw logs. Earlier evidence remains frozen.

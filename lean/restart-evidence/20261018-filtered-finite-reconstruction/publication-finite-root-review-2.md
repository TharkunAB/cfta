# Publication finite root reconstruction: corrected body growth

Date: 2026-10-18 12:49 CEST.

## Final source

The corrected source is `lean/MicroCFTA/SourceCurrentPublicationFiniteRootReconstruction.lean`.
Its SHA-256 is `bf4e1251f28e250904fe8959363dcc20db14485c13008321be1fc10c0af1f59b`.
The public declarations remain `BodyIH`, `publication`, and `writer`.

## Integration correction

The first frozen source had SHA-256
`a3406ec90ee2150864a4aaaf9ae99ba9233830e57673a1e6bf9b532325c9ff3f`.
Its body hypothesis covered arbitrary raw source calls without requiring
their return heaps to grow into the execution heap. That hypothesis was
stronger than the existing node-source induction producer could establish.
The old theorem remained conditional and mathematically valid. It did not
provide the intended composable node-body endpoint.

The corrected `BodyIH` adds exactly two premises after both raw equations:
`Grows rawHeap execution` and `Grows rawLater execution`.
The private `filtered` helper receives `Grows event.afterBody execution`.
It recovers both raw-return growth facts from the actual publication
callbacks and composes them forward into the execution heap. The public
`publication` theorem supplies this final growth from its constructed
sequential calls. No additional caller readiness, availability, future
completion, or desired output relation is required.

The hypothesis still covers only `event.expression`, the actual immediate
source body. The producer derives its strict size bound and lexical alias
certificate. It does not quantify unrelated smaller grammar expressions.
Its execution heap can extend the initial common heap. Its observation
reader remains fixed.

Both stored calls are constructed from initial `Keeps`, available
replacement, and available outer replacements. Both actual outcomes,
local publication histories, final warm replays, output availability, and
finite `RelatedAt` are retained. A shared sparse map uses actual
cross-absence. Unused lexical aliases need no global freshness.

`writer` still requires explicit installed selected-record evidence.
`Writer` alone provides the candidate callback cut and physical growth.
The selected record remains installed after both constructed calls.
No publication history is inferred backwards.

## Remaining boundary

The strict immediate-body source hypothesis remains an induction premise.
A literal active Mu atom still needs the corresponding strict source and
chronological-writer reconstruction case. This theorem does not establish
general retained-Mu alignment, finite-observation reader transport, or
outer termination. Arbitrary nested source syntax and captured values
remain in scope. There is no BinderFree or finite Cap restriction.

## Selected validation

`publication-finite-root-direct-4` has exit code zero and an actual
zero-byte raw log. `publication-finite-root-canonical-2` completes all 638
jobs without warnings. `publication-finite-root-public-2` prints all three
public signatures, full proofs or definitions, and axiom reports. It sets
all eight required options. The output has no omissions, printer failure,
warning, error, or `sorryAx`. Only the three standard axioms occur.

All selected checks use pinned Lean 4.34.1, a five-minute limit, and inner
readback of effective `memory.max=4294967296`, `memory.high=4294967296`,
and `memory.swap.max=0`.

Attempt 3 preserves a failed mechanical edit: it inserted the two growth
arguments twice in the private helper and omitted them in its local
`change` target. Attempt 4 fixes only that mechanical edit. Earlier
snapshots, logs, selections, reviews, manifests, and verification outputs
remain unchanged. The version 1 manifest is historical and unselected;
its live production-source and peak-file pins predate this correction.
The version 2 manifest selects the corrected source and fresh receipts.

This component contributes three public pairs and zero constructed pairs.
The independent checkpoint fixture validates the actual node-body use.
No root mutable working file or shared peak file is pinned here.

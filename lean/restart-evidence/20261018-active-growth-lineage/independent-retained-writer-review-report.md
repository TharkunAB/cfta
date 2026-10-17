# Independent review of retained Mu writer alignment

Read-only source review at 2026-10-18 01:30 CEST. No Lean build or proof source
change was performed for this review.

## Production result

No material mathematical defect was found in
`SourceCurrentRetainedMuWriterAlignment`.

The private source induction follows actual sequential build calls. It
retains the existing writer on a warm request, and it checks the literal
`afterBody.nodeRecords event.key` before publication. An already published
nested winner keeps its earlier writer. A genuinely absent record receives
the actual current Publication. The proof does not assign a losing current
candidate's syntax to an older selected record.

The source, many and row cases produce growth and issued-reference extension
from actual effects and reservation. They do not infer either fact from
`History.retain`, whose premise is only NoNewMu. Callback histories retain
the same fixed captures and the repaired ordinary marker
`ordinaryLevel depth = max depth.depth (freeBound depth.free)`.

The distinction between callback-cut evidence and selected membership is
important. `Writer` alone gives a candidate, its callback histories,
absence at its actual body cutoff, and growth plus issued extension from
that cutoff into the reader. It does not itself assert that the reader has
installed that record, or give an execution trace from publication to reader.
`source_writer` consumes actual selected membership. `retained` consumes
selected membership at the source return and returns retained membership at
the reader as a separate conjunct. Those public producers support the
selected-winner interpretation. Grows alone does not support it.

`retained` uses current physical coherence to recover the exact Mu request
key and installed entry. Its warm request has the same full depth and
ordinary fields, retains the reader state, and does not call the arbitrary
supplied callback. The selected stored payload, rather than a newly proposed
candidate, determines `finish`.

`Writer.reconstruct` and the reconstruction conjunct of `retained` require
BinderFree for the recovered writer expression. This predicate excludes
source binders in that expression. It does not exclude recursive values in
its captures, unrelated source binders, full guards or ordered child lists.
The initial source can be arbitrary. `initial` constructs its source return
and Ready internally, without a future successful source-build premise.
It does not prove that every recovered writer expression is BinderFree.
The unused-Mu readback is a separate unconditional consequence of the
existing causal closed-source theorem.

## Validation correction

The first reviewed production hash was
`eb890a9e9cecaef485567e0ef9039ecbc64b8cd41c42205509df8d5251e6f037`.
Its direct-4 log was 369 bytes and contained an unused-simp-argument warning
for `Option.getD_some`. Canonical-1 repeated that warning. Exit code zero
did not make that strict log empty.

The owner removed only that simp argument. The final production hash is
`7b90472203150878f29a7df43a0af2868f3789dd8a73427cb9d042284b98b6d0`.
Direct-5 is zero bytes. Canonical-2 completes 630 jobs without warnings.
Public-2 retains all seven explicit signature/proof/axiom pairs with all
eight required options. The old snapshot and warning logs remain present.

## Constructed fixture

The final printer-free fixture is `retained-writer-kernels-3`, source hash
`a59eb690e494c3c066d5dc3f35ac7caf0f12e6cbee943a6c828a8165cf6e0440`.
Its strict log is zero bytes. The selected printed group is
`retained-writer-kernels-public-1`, with two complete standard-axiom pairs.
These are two endpoints of one concrete source fixture, not two independent
source scenarios. The public production group is `retained-writer-public-2`,
with seven pairs. This review adds no proof-pair count and repeats no build.

The fixture constructs a raw Mu source from empty, with full Bool guards,
a union root and an ordinary node containing an ordered active child.
Its retained writer usesLocal test is true. A later smart binder has a
different source expression: it permutes and duplicates node rows and adds
an Empty suffix. It preserves the mixed node/reference union order.
Both literal source-build equations and the exact unchanged warm reader
state are proved. The fixture also supplies a deliberately different
callback that would return Empty; the selected nonempty body wins instead.

The generic recovered writer in the fixture still carries conditional
BinderFree reconstruction. A separately identified actual Publication has
its own proved BinderFree source expression and constructs both stored
reconstructions, with the original recursive Mu result as replacement.
This avoids assuming that an existentially recovered writer has the same
source syntax as the later requester. `initial_producer` instantiates the
own initial-completion endpoint on this same nonvacuous source.

The first failed fixture swapped the mixed union's node/reference order.
That change can affect raw intermediate records before self-filtering, so
an unchanged full-state equation was not justified by filtered key equality.
The final fixture keeps that order. The failed elaboration is not treated
as a proved counterexample or a production defect. Its original large raw
log is retained losslessly by the owner's archive. Fixture 2 then had only
unclosed negation goals, which fixture 3 closes explicitly.

## Remaining scope

The result discharges real earlier-winner provenance and source-derived
completion. It does not remove the recovered writer's BinderFree condition.
Arbitrary nested binder callbacks still require the remaining coupled
syntax and chronological-writer induction. Neither this result nor its
fixture proves initial general outer termination, runtime correspondence,
or physical equality of both reconstructed results. Reconstruction provides
physical-empty agreement and all finite full-row ordered observations.

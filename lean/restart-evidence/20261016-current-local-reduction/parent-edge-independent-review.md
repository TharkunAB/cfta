# Independent current parent-edge review

Reviewed at 2026-10-16 09:58 CEST. Source:
`lean/MicroCFTA/SourceCurrentAllocatedParentEdge.lean`.
Frozen SHA256:
`415caf6fc59d1c04d64ae93c51e4932c26e8031c84733e3caa622cbb5e008549`.

No material defect was found. The raw contradiction branch performs the
sentinel constructor without evaluating a local reduction. The separate
`rejected` theorem needs no child availability, current field load,
inherited readiness, or local range plan. The live branch constructs the
actual local reduction and then the checked edge at its literal returned
heap and equality-operation state. It retains the same actual reads and
returned merge/fourth/global tables.

The proof derives the original stored field's readiness and load at the
returned operation cache. It does not assume a future load. The nested
constructor receipt supplies the actual returned symbol, guard, and
children, including Top/[Empty] for rejection. Local length preservation
is not used to assert final checked-edge arity preservation.

Language narrows to the original raw edge unconditionally. Equivalence
requires satisfaction of the exact inherited payload. The zero-child
erasure case does not supply an invalid empty-language argument. No
result-language oracle or completed local reduction is a public finite
premise. Existing reached range plans and initial warm invariants remain
explicit.

The module is the reduced-edge BODY. It does not cover the source's
separate reduced-edge memo wrapper, inherited child continuation, outer
recursive node memo, general recursive termination, or GHC demand order.
The exact next target is recorded in `inherited-current-next.md`.

This review made no source edits and ran no build or new probes. The
existing owner logs report focused Lake success (1,390 jobs) and public
probes. Root separately reports a full Audit success (2,363 jobs and
56,924 theorem dependency checks). Those are owner-reported validation,
not independent reruns.

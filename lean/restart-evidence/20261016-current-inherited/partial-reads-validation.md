# Current partial-caller read schedules

Source: `MicroCFTA.SourceCurrentAllocatedPartialReads`.
SHA256: `a1e33b6191bee861816bd039b75b394c3910eb5b626bb3bcd5985a94f3d1292e`.

Eight mutual read graphs index the actual raw trace:
NodeCallReads, NodeBodyReads, EdgeCallReads, EdgeBodyReads, RowsReads,
DescendantsReads, ChildrenReads, and WalkReads. Each takes formulas, solver,
the actual raw trace, and the input/output three-family global bundles.
The raw budget and all actual caller-state indices are inferred.

Node and edge result hits retain the incoming bundle and skip body reads.
Evaluation follows the actual stored original body and its finish frame.
The ordinary body follows its ordered row reads. Empty, union, and binder
body schedules make no query-family call. The parent leaf contains exactly
the same actual SourceCurrentAllocatedParentEdge.Reads. Rows thread edge
call, returned-edge descendants, and row tail. Descendants wrap the actual
children schedule. Contradiction has no child call. Walk threads each actual
descended node request before its remaining slots.

No readiness, semantic answer, final validity, effect preservation, callback
law, or future completion is a read-graph field. node_hit, edge_hit, and
children_contradiction prove literal global-bundle equality in those branches.
These are operational query schedules. This module does not prove their
heap coherence or derive a SourceGlobalUnfold.Runs adapter for arbitrary
MuReconstruction.rebuild callbacks. It does not establish host forcing or
that a physical source cache corresponds to the logical serial tables.

Commands:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedPartialReads.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedPartialReads
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-inherited/partial-reads-public-probes.lean
```

Direct source terminal 0 with no warnings (`partial-reads-direct-3.log`).
Canonical terminal 0, 1,395 jobs (`partial-reads-build-1.log`). Only the old
unused inputs dependency warning appears. The earlier direct-2 log records
an incorrect toolchain path; it is not validation evidence.
Final public probes terminal 0, no warnings (`partial-reads-public-probes-2.log`).
Three public theorem axiom checks, eight complete family signatures, eight
kernel examples, and one explicit warm-fixture axiom check pass. Only
propext, Classical.choice, and Quot.sound appear. The explicit warm fixture
derives its begin answer from its literal returned cell. It is a protocol
fixture, not a claim of physical cache validity. The kernels also cover
evaluate-empty, contradiction on nonempty children, empty walks, two ordered
descended hits, exact ParentEdge leaf readback, and edge/descendants/tail
global chaining.

Public probe SHA256: `83e57c1011410b1a782ccb3c73bf173e3c1645ca7be758e183190db3d3b17593`.
Final log SHA256: `ff45159239d45cfcf84c84c86f38ee7a8676405f8b8f5be8779b15fac1894dd8`.
No old source was edited. No compiled evidence artifacts were made.
The module and API are frozen.

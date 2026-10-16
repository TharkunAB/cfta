# Historical primary receipt counterexample

Validated on 2026-10-16. This is a Lean receipt-model defect. It is not a Haskell defect.

The actual original constructor builds a resident closed ordinary root with one recursive child. Its root has positive cached depth. The completed constructor derives the actual heap Ready invariant and exact root availability. Empty unfolding, descendant, and predicate memo tables are initially valid.

The old EndpointMemoGateTrace.NodeReads.endpoint_closed constructor has independent implicit entries and edge lists for the indexed trace and its queried node. The witness attaches a literal completed query for ordinary identity 999, with no resident record, to the actual resident root trace. The final descendant table contains that nonresident input. Its global Valid predicate is false. The gate trace also yields an actual finite nodeMeets completion equation.

Public endpoints: 14 axiom reports and 14 full signature checks. Final public log exits 0. It contains no errors, warnings, or sorryAx. Only propext, Classical.choice, and Quot.sound occur. Direct source checks 2, 3, and 4 exit 0; failed direct-1 is retained. Direct-4 covers the final def-to-theorem warning cleanup.

Canonical validation: parent-actual-build-1.log records the final source build as target 1405/1407 and successful terminal completion. The only build warning is the existing unused inputs warning in InternedFreshOrdinaryClosedCompletion. Root's earlier scan-read-validity-build-1.log built the previous definition spelling; the final canonical log removes that defProp warning.

The independent strict-read kernels prove that this exact historical receipt cannot be a strict current receipt, and that the same actual resident trace derives a strict valid returned bundle. A third kernel composes exact primary reads with the actual secondary/seeded/current-conjunction query suffix.

Scope: no older file, Haskell file, Audit file, or Git metadata was edited. This witness does not assert a Haskell failure. Runtime identity, IO, lazy forcing, and publication remain external adapters.

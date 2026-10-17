# Scalar-only Merge integration

Reviewed at 2026-10-17 10:14 CEST.

The imported producer is `SourceCurrentMemoMergeUniformNumeric.lean`, SHA-256 `4fcc00803812b2839a0a122e8d82a21612bd49fbb764d4f41a7d1efb95624635`.
The kernel source is `merge-uniform-kernels.lean`, SHA-256 `d79d72fa70db794734d2b3036f3e002a934caefe9eb3535eb22fe40d813b685c`.
The successful raw log is `merge-uniform-kernels-1.log`, SHA-256 `a3a1e639e0a41368feb5bccfc14db732d443d37a184ee1f11a90987e015588b6`.

The four declarations construct literal source values from empty.
They derive Facts, available payloads, SemanticReady, and CostHeap from those same actual builds.
The initial mass is the causal heap initialBound.
The initial scalar is `ResourceControl.initialBound nodes.next edges.next mass`.
`ResourceControl.initial` derives Fits from that initial stored mass.
No completed Merge, intermediate Fits, future result bound, or result height is an input.

`ordinary_large` checks a real five-row ordinary group and constructs its own scalar-fuel call.
`recursive_large` checks a real five-row group with both an actual Mu child and an actual union child.
`recursive_boundary` checks that the productive recursive source is an actual Mu and constructs its own complete call.
Each complete fixture retains the exact Call, literal worker return, Effect, populated physical memo Stored, available result, final Fits, result mass bound, and stable larger fuels.

`cold_then_warm` constructs the first mixed call.
Its second initial scalar is exactly the first computed `workFuel` ceiling.
It passes the first returned Fits directly to the second producer.
It does not recompute fuel from a future actual result height or require an intermediate counter bound.
The first actual Call supplies the returned entry.
`hit_unchanged` identifies the second producer's result, whole heap, and whole memo with the first return.
The literal warm worker equality therefore retains that same populated table.

The absolute-path Lean 4.34.1 check exited 0 on its first attempt.
The log has no warnings, errors, sorryAx, or truncation.
All four declarations have full explicit signature and axiom probes.
Their only axioms are propext, Classical.choice, and Quot.sound.
The first exact source snapshot remains in `merge-uniform-kernels-1.source.lean`.
Large numeric ceilings remain symbolic.
These checks exercise sequential complete Merge calls.
They do not claim pending lazy publication, source concurrency, or complete Target/Force admission.
No production source or older frozen evidence changed.

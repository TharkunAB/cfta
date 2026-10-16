# Checked gate worker validation

Checked 2026-10-16 13:29 CEST. The owned source is `MicroCFTA/SourceCurrentAllocatedGateWorker.lean`, frozen at SHA256 `a1856994c9f009f6c46b8eb7cde632c7d3049d6938f54a1cb7479ca277bfaa90` (206 lines). No older proof, Haskell, Audit, documentation, or Git state was edited.

The parent built this module with its ScanWorker dependent and reported terminal exit 0, 1197 jobs, in `scan-worker-build-1.log` (handle 59545). The focused target was `MicroCFTA.SourceCurrentAllocatedScanWorker`, using the pinned Lake at `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build`. The owned direct source check returned exit 0 without warnings in `gate-direct-1.log`. This owner ran no additional canonical build.

The external probe commands were:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-typing-do-seeded-worker/gate-public.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-typing-do-seeded-worker/gate-kernels.lean
```

`gate-public-1.log` records exit 0 for 13 public axiom checks and 13 full signatures. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Universe annotations are printed explicitly. There is no `sorryAx`.

The final `gate-kernels-3.log` is empty and returned exit 0. Eight examples check empty classes at zero fuel; exact primary exhaustion; actual one-step reference results in both modes; exact pending key and returned heap; unchanged native node/edge/domain tables and operations; whole secondary return uniqueness; strict primary endpoint-indexed read validity; and finite secondary execution from initial semantic/cost/residency facts.

The first kernel log retains a probe-only simplification failure. The second retains an unused-section-instance warning. The final probe has a local unchanged-heap identity helper with that instance omitted. The proof source never changed after its first direct check. No compiled artifact is stored here.

The workers execute literal current `classMeets`. The primary graph proof uses `SourceCurrentMuEndpoint.primary_class`. The secondary graph proof uses `actual_current_class_trace_of_done`. Both retain the entire checked return and exact failure observations. Native tables, domain cells, and equality operations are retained. Fault does not depend on native width. Bounded `done none` and pending constructor observations remain distinct.

`primary_reads` constructs strict `SourceCurrentAllocatedPrimaryReads.ClassReads` from initial ranked gate readiness, original Values, and initial three-family Valid. It follows the actual graph and `lift_class`. No final validity or unanchored endpoint receipt is a premise. The worker has no fourth memo, merge result memo, or global bundle field. Reads are separate proof receipts.

Success stability and uniqueness require no physical or semantic premise. Finite existence uses initial SemanticReady, stored CostHeap, and original availability. No callback supplies gate completion. Whole scans, machine identities, containers, memo publication, and GHC forcing remain separate components.

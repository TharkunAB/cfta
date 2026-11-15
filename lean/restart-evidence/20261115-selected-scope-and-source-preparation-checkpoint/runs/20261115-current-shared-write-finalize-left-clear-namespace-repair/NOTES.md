# Namespace-only repair

Recorded 2026-11-15 01:47 CET. This candidate is UNCOMPILED.

The first strict check of source `095b60529b7273857e2ed24a28179bf0c0f704cba6ff8430a7e54a6e3742ca2a` failed at the unqualified `lookupNode` in the public header. The diagnostic is `20261115-actual-shared-write-to-clear-check/actual-incoming-finalize-callback-parked-clear-1.txt`.

This repair adds only `open SourcePruningEnumerationNodes` beside the existing namespace openings. The public theorem header and proof bytes are identical to the frozen original. The public finalizer export is now available. No premise, conclusion, runtime operation, or Haskell file changes.

The original packet's NOTES.md retains the full scope and remaining work. This proves no whole-history theorem or finite joint assignment. Root owns compilation and publication. No compiler, Git, board, Haskell, or /tmp operation was run here.

Probe: `MicroCFTA.SourcePruningEnumerationSharedBucketWriteToClear.written_bucket_removed_after_finalize_callback`.

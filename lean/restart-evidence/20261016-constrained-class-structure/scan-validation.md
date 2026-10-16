# SourceCurrentAllocatedFiniteOrdinaryScan validation

Recorded: 2026-10-16 17:08 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryScan.lean`. SHA256: `7555eb6cad3ed5d7ccb09dabd422fd3c58bed5ab95ac554573f0b4ed0beb022f`.

Actual primary node/child/path/class graphs return false at the identical heap. Strict primary receipts perform no memo calls. Every supplied current Scan selects the complete class list with outcome none and identical full checked state/fourth memo. The construct and verified endpoints produce strict ScanReads at the same global bundle. No proper-path, range, memo correctness, At, or global-validity premise is needed for these identity results. The literal current primary worker succeeds at every positive gate fuel.

Checks:

* Direct pinned Lean source check: exit 0, no warnings.
* Root canonical `depth-scan-build-1.log`: terminal exit 0, 1264 jobs. Only the historical dependency warning appears.
* 17 public axiom and full-signature pairs: exit 0.
* 3 imported integration axiom and signature pairs: exit 0.
* Final probes use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, errors, or warnings appear.

Three kernels check: supplied Scan preserves its own initial inventory At, native structural Stored, fourth Correct, and global Valid; two constructed scans preserve repeated classes and unequal path lengths at the same warm state; a reached node at gate fuel zero still returns the actual failed observation. The serial construction supplies no future successful graph.

Failed source checks are retained. Repairs only changed explicit proof arguments, a section-variable omission, proof transport, and Boolean simplification. The first isolated attempt had an incomplete local module search path. A temporary dependency symlink directory resolved that environment issue. The final source direct check and all final imported probes passed.

Imported commands use `LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean FILE`. Direct source checks used an isolated temporary olean directory. That directory was removed after imported validation. No compiled artifact is stored in this evidence directory. This component ran no Lake, Haskell, Git, Audit, or older-source operation.

This is a finite-ordinary source component. Mu, reference, and explicit-union inputs remain excluded. It does not establish general constrained outer termination, caller machine ranges, or GHC forcing/table correspondence. No Haskell defect is reported.

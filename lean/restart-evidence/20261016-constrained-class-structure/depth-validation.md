# SourceCurrentAllocatedFiniteOrdinaryDepth validation

Recorded: 2026-10-16 17:08 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryDepth.lean`. SHA256: `41b89ba37c6dad7c30b472a82a6a7905d6678e94b35f369e373f61859404a86f`.

Coherent available finite ordinary records derive depth=0. Existing free-name readback derives the literal fast metadata test. Guards and equality classes are unrestricted. Domain syntax alone does not constrain cached metadata.

Checks:

* Direct pinned Lean source check: exit 0, no warnings.
* Root canonical `depth-scan-build-1.log`: terminal exit 0, 1264 jobs. Only the historical dependency warning appears.
* 2 public axiom and full-signature pairs: exit 0.
* 1 imported integration axiom and signature pairs: exit 0.
* Final probes use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, errors, or warnings appear.

The integration kernel executes literal makeEdge and makeNode at an arbitrary initial semantic heap. It derives availability, finite-ordinary domain, cached zero depth, and empty free names for the actual returned node. The complete raw guard is an arbitrary parameter.

No source proof failure occurred. The first external kernel used the wrong context projection for Linked. The corrected kernel uses semantic.normal.facts.linked. The failed raw kernel log is retained.

Imported commands use `LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean FILE`. Direct source checks used an isolated temporary olean directory. That directory was removed after imported validation. No compiled artifact is stored in this evidence directory. This component ran no Lake, Haskell, Git, Audit, or older-source operation.

This is a finite-ordinary source component. Mu, reference, and explicit-union inputs remain excluded. It does not establish general constrained outer termination, caller machine ranges, or GHC forcing/table correspondence. No Haskell defect is reported.

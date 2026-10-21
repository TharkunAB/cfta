# Finite-call proof-verifier warning-header repair

Reviewed: 2026-10-21 22:40:12 CEST. SOURCE CLEAR for the complete fixed 147-line verifier, SHA256 0f200361256dff33d2f40da100fac77169e55be2e827143a9bbbee7ca03349b9. I personally read every fixed source line. This review ran no prepared verifier or proof command.

Exact forward and inverse replacement prove that only the total-warning assertion changed from 81ed5c29. The new regex anchors to a source-location diagnostic header and uses multiline matching. The unchanged actual strict2 raw has 15 such headers and 30 unanchored warning tokens, because 15 hint lines also end with the word warning and a colon. The 15 exact warning names remain the same, and the unchanged no-error/no-sorry checks hold on that raw. AST parsing and exact single-line diff identity pass.

No job inventory, receipt/source/raw pin, cap, usage gate, default strict limit, selected source, archive, live check, reader pin, FULL suffix, TYPE/body boundary, BYTE-identity pair, private marker/helper denial, raw axiom or Audit check changes. The repaired assertion now checks the intended diagnostic count without counting hint prose. It does not ignore an additional diagnostic warning.

The earlier broad-regex source clearance missed this metadata assertion. Its original source, original audit and the failed normal metadata run remain preserved. Root reports that metadata run terminal 1 at 2026-10-21T20:34:58UTC. This failure adds no Lean/Lake job. The actual proof ledger stays five jobs, one failed strict and one warned zero. Root must separately activate normal/live metadata verification after this source review. No rerun success is claimed here.

No previous audit, root-owned file, Lean source, proof evidence, compiler, runtime, capped, Git or network state changed in this review. All writes are confined to this new additive audit directory.

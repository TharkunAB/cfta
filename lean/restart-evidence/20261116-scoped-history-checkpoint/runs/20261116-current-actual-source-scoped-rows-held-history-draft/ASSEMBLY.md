Status: UNCOMPILED. No proof credit is claimed.

Use an ordinary owner source copy. Add REQUIRED-TOP-IMPORTS.lean.txt at the top.

Required append order:

1. Define the exact existing RealEagerHeldFragmentHistoryAtDepth once. Use the depth reference in Canonical's scoped ABI packet. Do not duplicate it.
2. Append 20261116-current-real-held-frame-scoped-abi-draft/DEFINITIONS.lean.txt under its matching preamble and namespace.
3. Append Canonical's projections and scope-safe helper in 20261116-current-real-held-frame-projections-and-forwarding-draft. This packet uses actual_held_frame_history_own and actual_frame_ledger_scope_safe.
4. Append Mixed's 20261116-current-selected-own-and-tuple-held-history-draft/APPEND.lean.txt. This packet uses the generalized own and direct tuple laws.
5. Append unchanged 20261116-current-actual-source-rows-prefix-resource-producer-draft/APPEND.lean.txt.
6. Append this packet's APPEND.lean.txt, then its appendable PROBES.lean.txt.

The old V1 task predicate and old accepted-row/full-rows proofs are not dependencies. Preserve those packets as provisional records. Other independent scoped components can precede this packet.

The source owner lacks the SharedScanOutputOrigins import at this pin. The ordinary top import has no owner dependency.

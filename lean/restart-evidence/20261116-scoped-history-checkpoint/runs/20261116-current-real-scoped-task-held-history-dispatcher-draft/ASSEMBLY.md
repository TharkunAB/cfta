Status: UNCOMPILED. All new scoped branch dependencies require strict checks.

Append this packet after the exact global depth predicate, scoped ABI and these branch packets:

1. 20261116-current-real-held-frame-projections-and-forwarding-draft: scoped tuple-cons and ordinary steps.
2. 20261116-current-selected-own-and-tuple-held-history-draft: generalized own and direct tuple history.
3. 20261116-current-actual-source-rows-prefix-resource-producer-draft: unchanged prefix resources.
4. 20261116-current-actual-source-scoped-rows-held-history-draft: complete scoped rows step.
5. 20261116-current-real-scoped-fallback-and-selected-nil-draft: scoped fallback and selected nil.
6. 20261116-current-real-captured-nil-held-history-scoped-draft: scoped captured nil.
7. This packet's APPEND.lean.txt, then PROBES.lean.txt.

Use the exact matching preambles for the scoped ABI and global depth definition. Define each predicate once. Retain the rows packet's ordinary TOP import SharedScanOutputOrigins in the source copy.

The old V1 structural task predicate and its dispatcher plan are reference material. The new theorem does not invoke the V1 target or assume its correctness.

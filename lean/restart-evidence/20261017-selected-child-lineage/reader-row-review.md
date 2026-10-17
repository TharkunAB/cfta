# Native reader row lineage review

Reviewed on 2026-10-17 at 23:57 CEST. Production source SHA: `2609deb0a873c845ff54dd5e47b867407c4bf80e7bcfb3a8d60f18ff9cebcba1`.

No material defect was found in `edge_returned` or `rows_child`. The retained source snapshot matches `reader-row-direct-2.source.lean`. That root-owned strict run has exit 0 and an empty log. This review ran no Lean job and adds no proof or integration count.

`edge_returned` uses the actual first instruction's `EdgeReady` and key-safety facts. Physical cache validity aligns a warm selected cell with the complete requested rows. The cold branch uses `edge_started` to obtain the same complete request. It preserves the captured evaluating owner through the exact edge-body trace and then uses the actual protected finish. Key equality alone is not used to identify arbitrary malformed operands.

`rows_child` first recovers the actual raw row schedule and normalizing constructor from the supplied completed `compileRows` trace. It aligns two decompositions of the same walk by deterministic successful execution. The indexed raw occurrence supplies its actual edge call and suffix.

The actual edge call yields an exact returned cell. The suffix and node constructor retain that same cell. The explicit `Retained after.native reader.native` premise transports it to the final reader. Only then does `History.writers` recover the causal writer. No `History` is assumed at the internal row-call entry, edge-call return, or active node-owner state.

The live-row premise is derived from actual node normalization. A sentinel row contains a literal empty child and cannot survive. The proof does not replace physical empty filtering with semantic emptiness. The historical writer then gives the full joined guard, exact symbol, ordered child index, and actual checked child-node trace. Its heap-growth facts refer to the chosen final reader heap.

The recovered child call belongs to the captured historical writer. A warm edge call can reuse a writer that precedes the current `compileRows` execution. The result does not place that historical child call inside the current active owner's body interval. It does not infer proper source-occurrence descent, all-active owner-key exclusion, or future completion.

The later retention premise remains explicit. The theorem is a completed-state lineage bridge. Actual trace retention or the retained-node-writer receipt must discharge that premise at a caller. The theorem does not itself construct the later execution or the final reader history. No Cap, whole-forest closure, result-origin callback, or future child-completion law is introduced.

A useful independent constructed test is an actual source-built ordinary query with nonnull ordered children. Retain the `compileRows` fragment while its node owner is active. Use history only at the final reader after the protected finish. A stronger second case should prepopulate the actual edge result by an earlier completed query, then force a new node owner whose row request takes the warm edge branch. The selected row's child trace should come from that earlier writer. Keep this test proposed until its own kernel passes. No explicit warm-hit or internal-history test was run by this review.

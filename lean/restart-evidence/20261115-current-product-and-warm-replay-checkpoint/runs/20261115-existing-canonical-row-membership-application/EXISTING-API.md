# Reuse the existing canonical row equality

Status: EXISTING PUBLIC RESULT. This small application example is UNCOMPILED. It adds no public theorem.

The exact API is InternedNodeSetCongruence.canonical_same, in lean/MicroCFTA/InternedNodeSetCongruence.lean at line 14. It already proves full canonicalEdges equality for two lists whose rows are resident in one coherent heap and whose edge-identity membership is equal. Facts.coherent supplies its coherence requirement. Full physical row membership equivalence gives identity membership equivalence by List.mem_map in each direction. The application file gives the requested goal directly from that API.

The existing proof uses canonicalEdges_ids, EnumerationBuilderCaches.canonicalIds_equal, and InternedEdgeResidency.edge_lists_equal. The last helper uses edge_identity_unique: two complete resident rows with the same identity in one coherent cache are equal. Therefore the result identifies complete EdgeValue records and ordered children, not only IDs or edge keys.

This is a finite canonicalization fact. It permits different raw row order and duplicate counts. It does not equate or change the raw lists, remove occurrences from their actual trace, or prove the needed membership premise for a pairscan. Retain every raw occurrence through actual execution; use this equality only at the canonical lowering boundary.

For the actual pairscan/diagonal application, the remaining obligations are explicit: prove both full row lists resident at the SAME actual returned heap, and prove their actual complete-row membership equivalence. Residency in unrelated extensions does not suffice. No semantic model, cache framework, future result provider, or native execution theorem is involved.

The original full coupled header is copied byte-identically. Its historical OPEN comment is retained. No Haskell, live source, compiler, Git, board or tmp changes were made. Stop after this packet.

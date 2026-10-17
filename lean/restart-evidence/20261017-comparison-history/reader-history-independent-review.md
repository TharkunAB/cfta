# Independent reader history review

Reviewed 2026-10-17 09:08 CEST. No material issue found. Final source is e7c92463f91abb1f2024aa63429944b298d42e2af8d56a96fa455e289656f728.

`SourceCurrentAllocatedReaderHistory.Run.history` follows the actual consumed graph. It derives each next physical invariant from the exact collector step. Only an actual fresh Mu branch adds an unfold event. Empty, ordinary, union, and seen branches keep the same full heap, so their remaining histories need no event. Allocation-free successful Mu unfolds remain actual recorded events.

`collect_history` extracts the exact consumed run from the supplied successful collector equation. It does not infer effects from final counter differences. Canonical row normalization changes no heap; `canonical_history` uses the original row list only for the collector witness.

`nodeEdges_history` follows literal reader order. Ordinary cases return the identical heap. Union cases collect the original union. The Mu case obtains the exact deterministic unfold and records it first. The physical singleton step retains the fixed degree limit. If the result is an ordinary node, the actual returned heap is that middle heap. Other results trigger collection of the ORIGINAL Mu at that middle heap. The original Mu remains available through actual growth and issued history; its closedness is unchanged. Thus the fallback history starts at the correct complete middle heap. `read_history` only converts the actual result wrapper and keeps the same rows and heap.

All4 public declarations pass imported full signature and axiom checks. Two strict-clean integration kernels construct their own initial source, readiness, causal mass, and numeric row read. One source is an actual raw Mu. The other is an actual union containing a Mu, with its shape proved by reduction. Each extracts a cold history and an exact full-heap warm history. Their concatenation derives the SAME original history ceiling, independently of the row-read fuel. The kernels also retain warm replay at larger fuel.

Production direct2 is empty and canonical1218 jobs pass. The canonical log replays the older ClosedCompletion unused-variable warning. The new source and standalone probes have no warnings, admitted proofs, or truncated signatures. Direct1 source and log remain preserved.

These are histories of supplied actual reader equations. The kernels independently construct those equations through initial numeric completion. This module does not supply enclosing comparison or selection fuel. No general Operand forecast or whole-library correspondence is claimed.

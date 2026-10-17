# Stored call and row producer review

Sources: Calls c5173341c68ebbba87cad9bced57c6f0d16648767a089286142852c9ccad522c;
Origins 566cd24ca2451b34484c4e69cfb7134c53840fa6007b96f0da1a2067faae4460.
Independent read-only review found no material issue.

from_encoded rewrites each literal child equation at its own reached heap.
It retains the original environment and exact prefix/suffix calls. It does
not substitute a hypothetical call at the original initial heap.
NodeRows maps a normalized output row to an existential source/rebuilt
occurrence. It does not claim uniqueness, injectivity, or normalized order.
It retains actual makeEdge, complete symbol/guard, and ordered child arity.
UnionRows concerns actual substituted member returns and their heaps.
node_complete/union_complete construct success from initial semantic heaps,
coverage, and source/replacement availability. They retain the closed
identity branch and derive causal History from actual source execution.
No shallow or no-Mu restriction is present. Retained-Mu recursive provenance
remains open. The new physical-equality counterexample is not a Haskell defect.

Root constructed checks use an actual source-built open node containing a
raw inner Mu and then an actual union containing that node. Both initial
completion producers return their row receipts and causal histories.
All root final source/public/kernel checks pass. Failed attempts retain
raw logs and exact snapshots. No prior evidence directory was modified.

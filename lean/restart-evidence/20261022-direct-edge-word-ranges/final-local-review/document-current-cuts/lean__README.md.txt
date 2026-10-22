# cfta formal model

## Word ranges for direct edge-body prefixes

Updated: 2026-10-22 03:41 CEST. Proof checkpoint: `3ad63b6b39`.
Start: `108bc09e80`. Imported main remains `794903b3f`.
Read `lean/notes-current-direct-edge-word-ranges.md`.

SourceCurrentAllocatedDirectEdgeWordRanges.edge_body derives WordRanges
for every raw Steps prefix of the exact empty-domain edgeBody request.
It uses the SAME Checked(bits+2) state, fixed source Facts, current Good,
SemanticReady, Grows, source history, exact EdgeScope and current EdgeReady.
Room uses source.nodes.next, source.edges.next, current domains.next and
literal mass 0. It does not supply runtime completion or a semantic law.

H11 semantic Completes remains a separate theorem. H6 constructed_node_calls
remains the strongest combined semantic result. Native completion, practical
host width, public Mu/full-pass and Haskell refinement remain open.
The whole formalization goal stays active and incomplete.

Preservation covers 82469 baseline files/modes, 298 baseline Haskell files,
207 active package files and all old evidence. Only the Audit import and
nine additive doc prefixes may change old files. FINDINGS retains its
Haskell repair index FIRST. Any new Haskell archive must match baseline bytes.
The preceding 108bc09e checkpoint is local only. Remote publication remains
PENDING_USER_APPROVAL after automatic review rejected earlier pushes.
This checkpoint publication tool performs no push or network command.

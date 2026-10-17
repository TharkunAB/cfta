# Selected child lineage review

Checked on 2026-10-17 at 23:55 CEST.

The review found no material defect in `SourceCurrentSharedEditChildLineage` at source SHA `822fd3d96648267efd014547599b94530b9ce98e6d3c615831a94f8c2bfca4d0`.

`Slice` and `indexed` retain the exact input/output child position. The earlier scan starts at the original offset. The later scan starts at `offset + index + 1`. Their captured checked states and global memo bundles follow the actual selected or unselected dispatch. The proof does not infer chronology from identities.

`selected` derives prefix availability and safety from the original list. The actual prefix returns the readiness and valid memo bundle used for the selected node. Populated edits derive the selected subtree's `HasLeaf`. The selected node receipt retains the original untouched suffix, and the suffix effects give the final growth. Native history is produced by the actual prefix and node reads. No future child-completion or history law is assumed.

`row_child` obtains an actual earlier-row prefix from normalized row membership. It derives row-start readiness, availability, memo validity, and history from that prefix. It then composes the selected node and remaining child scan with growth from the row constructor to the final reader. The source row and source child indices remain separate. Full guard and symbol equality come from raw constructor readback. The normalized output index is not claimed to equal the raw source row index.

The integration copies only the initial fixture from frozen `shared-edit-row-kernels-7.source.lean` into a new namespace. It uses actual source-built `left` and `right` values and an unselected open depth reference. The initial equality-operation cache is valid and contains its prepared descent entry. The edit map selects children 0 and 1 with original class tokens `[0]` and `[1]`.

The test derives its own finite width from the initial edit-list forecast. `SourceCurrentEditListNumeric.complete` constructs the actual complete child scan. `selected` extracts index 1. `indexed` decomposes its one-child earlier scan. Empty prefix and suffix read equations align the first leaf's entire returned shared state and global memo bundle with the second leaf's entry. Both selected calls retain full `Leaf.Receipt` values. Each receipt contains an actual force and a checked native `TargetQuery.Step`. These are real leaf branches, not empty-node branches. The theorem also derives captured readiness, both native histories, and chronological heap growth. It takes no completed future graph, future history, Cap, whole-forest closure, or successful worker premise.

The selected strict check is `selected-child-kernels-2`: exit 0 and an empty log. The selected imported group is `selected-child-kernels-public-1`: one complete signature, proof print, and axiom report. The final probe contains all eight explicit options. All own attempts record 4294967296-byte memory max/high and swap max 0. Attempt 1 remains immutable and failed during fixture elaboration. Attempt 2 corrected local equality and list-lemma uses without changing the production module. The peak was 251 MiB.

The integration tests selected child sequencing. It does not claim an explicit native warm hit or a new normalized row-survival fixture. The general `row_child` theorem was reviewed separately. This component does not prove all-active owner-key exclusion, outer recursive completion, or Haskell runtime correspondence. No Haskell defect was found.

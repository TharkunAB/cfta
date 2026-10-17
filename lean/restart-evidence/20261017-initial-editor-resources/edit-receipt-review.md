# Exact current-inventory edit receipts

Reviewed 2026-10-17 11:14 CEST.

`ready` changes only the current admission inventory. Its supplied complete
Frame refers to the SAME returned checked state. The captured base, physical
Merge store, semantic coverage, target table, and historical slot receipts
remain unchanged. Historical slot inventories remain independent witnesses.

The common and three specialized receipt adapters retain every physical
state, read, extension, slot, memo, global table, and positional domain fact.
They replace only current readiness and admission with the returned Frame.
The node, children, and rows wrappers first use the existing actual read
verifiers. They then remove the verifier's existential current inventory by
using the caller's complete Frame at that exact return.

These are compositional verification lemmas. The wrappers take actual Reads
and a returned Frame. They do not construct an edit or derive its final Frame.
They introduce no supplied Leaf callback law or desired result Cap.
The initial safety, population, allowed tokens, and global validity conditions
remain the exact existing physical verifier conditions.

`rows_length` counts every raw row occurrence before node canonicalization.
Its proof follows the actual mutual edit graph. `node_children` weakens each
ordinary child's Cap to the supplied parent depth. The zero-depth case uses
hereditary annotation. The positive case uses the smaller child Cap.

The imported integrations construct an unselected child scan and a nonempty
raw-row rebuild. The rebuild derives its final Frame and numeric bound from
actual constructor work, then obtains the existing full RowsReceipt at that
same inventory and heap. Neither kernel assumes a completed-read conclusion.
No Haskell source changed. No Haskell behavior defect was identified here.

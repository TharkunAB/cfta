# Shared edit row lineage review

Checked on 2026-10-17 at 23:38 CEST.

The review found no material defect in the three row-lineage theorems or the parent writer-history bridge.

`children_indexed` retains the exact child index. Its selected branch gives an actual `EditNode`, not a future completion promise. This pure theorem does not itself give child reads.

`rows_indexed` advances the returned global memo bundle through the actual edge constructor. It derives the next `Valid` from that bundle and the constructor effects. The selected row carries its exact earlier `EditRows` prefix and `RowsReads`. The source and result row indices agree before node normalization.

`node_survivor` uses actual constructor readback and normalized membership. It derives a raw row index for each surviving result row. The source index is existential. Sorting and duplicate removal do not preserve the normalized output index. Full symbol, full guard, ordered children, captured readiness, and heap growth remain exact.

The parent bridge runs the actual earlier-row prefix to derive history at the captured row start. It then runs the actual child reads to derive history at the row constructor. It does not assume either captured history as a future result.

The integration copies the initial physical fixture from the frozen `edit-numeric-kernels-14.source.lean` into a new namespace. It constructs the original values, a valid equality-operation cache with a completed descent entry, an empty shared target state, and full readiness. The fixture allocates two live rows with different symbols and the full guard `some [[[0], [1]]]` with formula `top`. Each live row has children `[left, right, depth-reference]`. The third child is open and unselected.

The raw source order is `[second, dead, first, second]`. The dead row has one additional empty child. Index 3 selects that empty child through a populated edit subtree. The actual empty-node edit and the unselected branches are both constructed. The raw constructor outputs equal the source rows. The final node constructor uses canonical row normalization. The test proves that the first live row survives and that the dead row does not survive. It does not assert a fixed normalized output index.

The four selected integration declarations are `initial_rows_and_selected_child`, `indexed_row_prefix`, `normalized_survivor`, and `survivor_writer_histories`. The third raw row has an exact two-row execution prefix. The last declaration derives initial native history from the actual source state and constructor growth. It then obtains both captured histories from the parent bridge. No public integration takes a completed graph, future read, history, Cap, or whole-forest closure premise.

The selected printer-free check is `shared-edit-row-kernels-7`: exit 0 and an empty log. The selected full-proof group is `shared-edit-row-kernels-public-1`: four signatures, four checked proof prints, and four axiom reports. Every final source has the eight explicit probe options. Both runs record effective memory max/high of 4294967296 bytes and swap max 0. Attempts 1 through 6 remain immutable. Attempt 5 checked the first three integrations before the history bridge was added. Attempts 1–4 and 6 failed during fixture elaboration and are not selected.

This is completed-edit lineage and causal writer-history transport. It does not prove proper original-source occurrence descent, all-active-owner key exclusion, outer recursive completion, or GHC runtime correspondence. It does not add a Haskell defect.

# Compiled decoder offsets

`DecoderDispatch` follows `offsetParts`, `dispatchParts`, and `compileTable`
in `Ranked/Internal/Decoder.hs`. It represents the ordered map by its ordered
entry list. Compilation builds a binary tree. Each split takes half the
entries and compares against the first offset in the upper half. Each leaf
passes the global rank minus its offset to its stored decoder.

`build_total` derives a sufficient finite compilation bound from the table
length. `build_spec` proves that compilation retains every entry in order
and gives each pivot the required partition. `select_exact` compares the
compiled traversal with the independent last-eligible-offset specification.
It does not assume that an unspecified dispatcher chooses the correct branch.

`offsetParts` skips zero-count branches and advances by positive counts.
`offsets_sorted` proves the strict ordering required by
`Map.fromDistinctAscList`. `offsets_exact` proves branch selection and local
rank against a separate linear count-subtraction algorithm.
`source_dispatch_exact` composes these results for every valid rank.
`choice_decode` derives exact lookup in the concatenated branch member lists.
Duplicate values remain separate ranks. Empty alternatives remove no member.

`locate_bounds` proves that every returned local rank is inside its selected
branch. `offsets_upper` bounds every stored offset by the complete count.
`machine_bounds` derives the range obligations when the source chooses its
small decoder from a checked total. It proves mathematical bounds; it does
not implement the GHC signed-integer representation or its conversion.

`DecoderDispatchCost` instruments the same compiled selection. It derives
the logarithmic comparison bound from the actual half-table construction.
See [the cost notes](notes-decoder-dispatch-cost.md).

The model uses natural counts. Source producers must supply consistent,
nonnegative cardinalities and valid decoder callbacks. Physical Map layout,
machine conversion, tabulated arrays, shared callback storage, and Haskell
closure compilation remain representation boundaries. Lookup comparison
counts exclude those costs and the cost of the selected branch decoder.

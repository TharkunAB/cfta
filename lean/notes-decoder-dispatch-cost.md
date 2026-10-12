# Compiled decoder dispatch cost

`DecoderDispatchCost` counts the rank comparisons in the binary closure tree
built by `Ranked.Internal.Decoder.compileTable`. A leaf performs no dispatch
comparison. Each split compares the rank with its pivot once.

`measured_result` proves that this instrumentation keeps the selected entry.
`half_lengths` proves the bound for the actual `take (length / 2)` and
`drop (length / 2)` branches. `build_depth` then derives the tree-depth bound
from successful execution of `DecoderDispatch.build`. It assumes no output
balance invariant and requires no ordering hypothesis for the cost bound.

For any successful table compilation, if the table has at most `2^bits`
entries, every lookup uses at most `bits` comparisons. The explicit bound
is `ceilLog2 n`: zero for zero or one entry, and `log2 (n - 1) + 1` otherwise.
`ceilLog2_covers` and `ceilLog2_le` prove that this is the least suitable
nonnegative exponent.

`leaves_le_power` proves the matching lower bound for any binary decision
tree. `build_depth_exact` shows that an ordered compiled table has maximum
route depth exactly `ceilLog2 n`.

`offsets_length` derives the entry count of the actual source `offsetParts`
operation. It equals the number of positive-cardinality branches; zero-count
branches do not contribute entries. `source_dispatch_with_cost` combines
that result with the source dispatch theorem. For every valid rank, the
compiled lookup returns the specified branch and branch-local rank within
`ceilLog2 positiveCount` comparisons. `source_dispatch_bits` gives the
power-of-two form directly. No desired decoder law is a premise.

## Boundary

The count covers pivot comparisons during lookup. It does not count
compilation, map construction, offset subtraction, branch decoder work,
allocation, or the bit cost of integer arithmetic. The source's machine
integer range, concrete offset-map representation, and callback behavior
remain separate interfaces. The theorem does not claim that compilation
cost is logarithmic.

## Validation

`lake build MicroCFTA.DecoderDispatchCost` checks the module and its
`DecoderDispatch` dependency. Principal declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

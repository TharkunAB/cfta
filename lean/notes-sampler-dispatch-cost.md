# Weighted-ticket lookup cost

`SamplerDispatchCost.measured` executes the actual upper-midpoint search in
`Sampler.compileWeighted`. It also counts comparisons between a ticket and
a group start. `measured_result` proves that this instrumentation returns
the same group index as the existing source worker.

`halves` derives the sizes of both search intervals from the actual midpoint.
`measured_bound` proves that an interval with at most `2^bits` entries takes
at most `bits` comparisons. `compiled_comparisons` derives the nonempty-table
condition from successful compilation and gives the bound
`ceil(log2(group count))`. Groups contain outcomes with equal ticket widths.
Thus lookup comparisons depend on the number of distinct widths, not the
expanded ticket count.

This theorem counts search comparisons. It excludes weight normalization,
group-map construction, array allocation, the random draw, and arithmetic
cost. Existing sampler theorems prove ticket probabilities and array-index
bounds. This module does not claim that compiling arbitrary rational weights
or producing random bits takes logarithmic time.

Validation: the pinned `lake build MicroCFTA.SamplerDispatchCost` succeeds.
No Haskell source changed.

# Source constraints and the complete symbolic index

`SourceSymbolicIndex` composes the source guard adapter with the allocated
symbolic count, decode, and inverse workers. The accepted language checks
both stored equality classes and the current complete public guard evaluator.

`CompiledRows` records the exact output of successful source compilation.
It does not assume an indicator semantics. `compiled_score` derives that
semantics from `SourceIndicatorCompiler.successful_constraint_score`.
Unsupported theory and substitution guards therefore remain explicit errors
in this solver-free route. This theorem does not silently classify them as
false or discard their terms.

`source_index` gives one cardinality and one sufficient execution bound.
At every larger bound, the source cardinality is exact. Every rank in
`0 .. count-1` decodes to one accepted term. Every accepted term has exactly
one rank, and the source inverse returns that rank. Each rejected finite
term has a sufficient inverse bound after which the source rejects it.
There is no premise that assumes these whole-worker properties.

`workerIndex` records the actual source decoder order with `List.ofFn`.
Its distinctness and exact coverage follow from the proved worker results.
The final theorem equates source `unrank` with this index's decoder and
source `rankOf` with its encoder. The fallback in the total observation
function is unreachable at every valid rank.

This list is a proof artifact. The source symbolic decoder still selects
with counts; it does not build this list. Existing worker cost theorems
apply separately. In particular, overlap preprocessing can be exponential.
Neither this composition nor a finite execution bound gives a general
polynomial running-time bound.

`source_probability` gives the requested mass at each distinct decoded term.
`source_probability_normalized` proves normalization for nonnegative weights
with positive total mass. These theorems attach a requested term law to the
actual decoder order. They do not assert that every existing generator
facade accepts arbitrary term-weight functions. Ordinary generator members
can retain equal values or terms, and their probabilities must be summed.

The remaining inputs describe concrete row readback: successful indicator
output, copied intersection/conditioning/projection rows, and finite interned
allocation histories. The existing graph modules prove their pure workers.
The Haskell runtime, host stores, and complete source extraction remain
representation interfaces. The theorem does not remove these interfaces or
claim whole-Haskell verification.

Validation: the pinned `lake build MicroCFTA.SourceSymbolicIndex` succeeds.
The aggregate audit checks all theorem dependencies. No source code changed
for this composition.

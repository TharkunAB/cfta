# Numbered subterms for acceptance caching

`NumberedTerms` follows `Internal.Tree.acceptsBy.positioned`. Each numbered
node retains its original subtree. The counter advances before the children
and then passes through the children from left to right.

`number_original`, `numberForest_original`, and `number_valid` prove exact
subtree and child-order retention. `number_next` proves that the counter
consumes one position per constructor. `number_positions` gives the exact
contiguous preorder range. `numbered_positions_unique` proves that distinct
positions cannot collide in the acceptance cache. `numbered_position_bounds`
gives the allocated interval.

The source cache also includes the automaton state in its key.
`AcceptanceDispatch`, `AcceptanceEffects`, and `AcceptanceSoundness` now prove
both workers, their caches, and sound definite verdicts. An
external monadic guard check must have stable truth at a fixed state, edge,
and term if memoized results are to describe a language. The source counter
uses `Int`; the numbering correspondence requires that the term's constructor
count fit the available nonnegative range.

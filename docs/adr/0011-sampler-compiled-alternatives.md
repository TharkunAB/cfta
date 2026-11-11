# 11. A recursive sampler keeps its compiled alternatives

## Context

A `Sampler` is two fields, and each field is a function of the sampling
backend (`forall gen. GenBackend gen => gen a`). A field is thus not a value
that the runtime keeps: what one draw shares with the next draw is what the
optimizer moves out of the function. `GenBackend` has an `Applicative`
superclass and no `Monad`, so a weighted choice could not draw first and
build second: it gave `frequencyGen` the generators of all its alternatives.
For a recursive generator with weights (`frequency`, `withWeights`, a
weighted atom below `recur`), the same source then had two behaviours. The
optimization level and the shape of the program selected one of them:

- The tables stay. Each QuickCheck table of generators keeps the
  alternatives that a draw forced, and they keep their own tables. The
  sampler grows towards the tree of the language, by size and by path.
  Without optimization, which is how this repository builds for development
  and for tests, binary trees with weighted leaves had 60 MB and 84 MB of
  live data after 40,000 and after 80,000 draws at size 13, and 680 MB and
  1,257 MB at size 25. With `-O2`, the sampler of `rankedCompletions`
  (`Data.CFTA.Sized.Prefix`), which reads the samplers of its states from a
  lazy table, had 119 MB after 80,000 draws at 13 nodes, and 905 MB after
  40,000 draws at 25 nodes.
- Nothing stays, and each draw builds again the table of each node that it
  visits. With `-O1` and `-O2`, a draw of the binary trees cost 190
  thousand instructions at size 13, 8.6 million at size 101, and about 180
  million (8.4 ms) at size 401.

Other samplers do not have the problem. A uniform recursive generator
selects one rank and decodes it. An atom compiles its weights to a ticket
table when it is built.

## Decision

A recursive sampler keeps its data outside its fields, and a draw selects an
alternative before it builds a generator.

- A choice and a product compile their alternatives one time for each size
  class, to data that has no backend: the weights, their ticket table, and
  the samplers of the parts. The two fields share this data.
- A choice and a product keep the sampler of each size class in a lazy list
  by size (`memoSampleIndex`).
- `GenBackend` has a method `selectAlternative`: select a position by
  weight, then run the generator of that position. Its default is
  `frequencyGen` on the generators of all the positions, and the default is
  its specification. `Exact` uses the default. QuickCheck draws the ticket
  that `frequencyGen` draws, and builds only the selected generator.

## Why

- Sharing is then a property of the source, not of the optimizer. With
  `-O0`, `-O1` and `-O2`, the live data of the binary trees stays at 0.2 MB
  at sizes 13 and 25 for each count of draws, and a draw at size 13 costs
  106, 57 and 56 thousand instructions. With `-O2`, the sampler of
  `rankedCompletions` holds 0.4 MB, and a draw at 25 nodes takes
  8 microseconds, against 95 microseconds.
- A draw does the work of one path through the language: with `-O2`, 56
  thousand instructions at size 13, 586 thousand at 101, and 3.5 million
  (0.25 ms) at 401.
- The distributions and the draws stay. The `Exact` meaning of each
  combinator is the same list of outcomes. QuickCheck gives the same value
  for each seed, so each checksum is the same.
- The package has this rule for its other data: an atom compiles its
  weights one time (`compiledWeightedSampler`), and `toGen` keeps a lazy
  list of the bounded generators by size.
- The standard generator cells have no weighted recursive sampler. They
  stay within 0.005 % in instructions and 0.003 % in allocation.

## Consequences

- A sampler keeps its tables while its generator is live. The tables hold
  the splits of each product at each size class that a draw visited, and a
  split has big integers: its count, its rank offset, its weight, and its
  ticket bound. For the binary trees the tables take 0.2 MB at size 25,
  2.2 MB at 101, 10 MB at 201, and 54 MB at 401. The count of the draws
  does not change this.
- The first draws at a size pay for the tables: about 2.1 billion
  instructions at size 401, which is 12 draws of the old sampler.
- A backend that draws one outcome must define `selectAlternative`. With
  the default, the backend is correct, and it builds each alternative at
  each draw.
- A formal model of the samplers has four more laws: the selection law of
  `selectAlternative`, the law of the ticket table, the law of the compiled
  alternatives, and the memo law. The header of
  `Data.CFTA.Ranked.Internal.Sampler` states them. The `Exact` model of
  each combinator does not change.
- `Data.CFTA.Gen.Internal.Join` had a map of the samplers of a join by
  size. The memo of the choice replaces it.

## Discussion points

- A `Monad` superclass, with a method that selects a position, gives the
  same draw as a bind. It changes the superclass of each backend, and the
  model of `Exact`, for one use. `selectAlternative` is that bind for this
  one shape. A ticket table shared inside the QuickCheck `frequencyGen`
  alone still builds the generators of all the alternatives at each draw.
- A sampler for one backend (the backend as a type parameter) makes each
  field a value that the runtime keeps. With tables of generators, that is
  the growth of the unoptimized build at each optimization level. Flags
  and pragmas (`-fno-full-laziness`, `oneShot`, `NOINLINE`) also select one
  of the two old behaviours.
- A deep embedding, with `Sampler` as a data type that each backend
  interprets, is the direct form of "a sampler is a plan". It is a rewrite
  of the lowering for the same draws.
- A memo only at the recursion knot (`fixSampleIndex`) does not share the
  splits of a product below a choice: a child is compiled one time for
  each slot of its parent.
- A table that each draw reads costs more than alternatives that hold the
  samplers of their parts: 68.8 thousand instructions a draw at size 13
  for a binary trie by size, 60.6 thousand for a list, and 56.3 thousand
  with no lookup. The sizes are small and dense from zero, so a list is
  sufficient.
- The digits of the big integers are 62 % of the table memory at size 401.
  A product with weights that are counts has its rank offsets again in its
  ticket table, and the list of the weights serves only the default
  `selectAlternative`. To drop one of them needs a second selection path.
- The uniform sampler of a recursive generator selects one rank and decodes
  it: 4.0 ms a draw at size 401, against 0.25 ms for the weighted walk. A
  walk by count has the same distribution, and gives another value for
  each seed.

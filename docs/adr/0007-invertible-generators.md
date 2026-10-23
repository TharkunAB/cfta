# 7. Two routes give term-to-rank: invertible blocks and support-guided ranking

## Context

The Index goal says that rank and term are inverse maps. `Gen.unrank` decodes a
rank. An automaton import has the other map, `Gen.rankOfTerm`, because its
engine term is the accepted user term. A generator built from combinators
(`elements`, `node`, `oneof`, `<*>`, `fmap`) has no such map. Its engine term
holds the structure of the combinators: the choice index, the applicative
spine, and, after `Gen.Refinement.compile`, the exact refinement labels and the
keyed joins that the symbolic count needs. A user term has none of these. The
applicative `<*>` cannot give an inverse either, because its left side is a
language of functions.

## Decision

There are two routes, by how the generator is built.

- A static generator uses invertible blocks. A block can carry the inverse of
  its values: `OutcomeIndex` has a field `outcomeRankOfValue`. The blocks that
  have one are `invertible` (a source with an inverse), `invertibleMap`,
  `invertiblePair`, the choices (`oneof`, `frequency`), `pay`, `node`, and
  `atomic`. `rankOfInvertible` reads it for a finite generator. A plain `fmap`
  has no inverse, and the generator then has none. This is opt-in: a user
  builds the generator from these blocks.
- A compiled refinement generator uses support-guided ranking.
  `Data.CFTA.Gen.Refinement.ranksOfSurface` matches a term against the support
  of the generator, builds the engine terms whose surface is the term, and
  ranks each of them with `ranksOf`. The term has ordinary symbols: a
  constructor by its name, and an integer leaf by its integer.
- An automaton import keeps its own route, `rankOfTerm`.

## Why

- Static generators have no hidden structure, so an inverse at the value level
  composes: the inverse of a product is the product of the inverses, and the
  inverse of a choice is the union of the inverses of its alternatives, moved by
  the offsets.
- A compiled engine term cannot be the user term, because the count needs its
  extra structure. The support of a compiled generator is a small graph of
  shapes, also for a million integers, because the integers are open variables
  in it. The surface of an engine term (`surface`) drops the private nodes, so
  the user term is found by a match of the surface against the shapes.
- Support-guided ranking ends in `ranksOf`, the code that `unrank` is checked
  against. The ranks are the same ones, and `ranksOf` rejects a wrong candidate.
  The integers bind where the match uses them, and a constructor takes its exact
  label from the integers under it in the order of the engine term, as
  `compile` fills a term. The match does not assume that the order of the term
  and the order of the engine term agree.
- The cost of the match is the size of the term times the number of shape nodes
  for each symbol, and it does not depend on the integer domain. A new function
  adds no cost to a generator that does not call it. No production path changes
  for the compiled route.

## Consequences

- Every `OutcomeIndex` has one more field (invertible blocks). `frequencyStatic`
  builds one more thunk. On the eight standard cells the allocation changes by at
  most +0.09% (`lta-do 20`), and the checksums are equal.
- A value that appears in two alternatives of a `oneof` has two ranks, as
  `oneof` counts it twice. Both routes give all of them.
- A generator built with `<$>` and `<*>` has no `rankOfInvertible`. The user
  chooses the blocks. A compiled generator has `ranksOfSurface`.
- `ranksOfSurface` reads the support, so it works for a finite generator and
  for an import with a cycle whose cycles pass through a labelled node.
- The names `rankOfTerm`, `rankOfInvertible`, and `ranksOfSurface` stay
  different in this decision. A unified name is a follow-up.

## Discussion points

- Keep the user term as the support, as an automaton import does: rejected for
  combinators. It would remove the keys and the refinement labels of the engine
  term, and the symbolic count of `compile` depends on them.
- A search over the members of the generator with `termAt` and `rankOf`:
  rejected, because the rank order inside a size class has no key and the
  search lists the members. A search over the shapes of the support is a
  different search, and the decision uses it: its size does not depend on the
  members.
- Propagate the inverse through each grouping layer of `compile`: rejected.
  (1) A value's group depends on the exact labels at the roots of its children,
  so every block would also need a function from a value to its label.
  (2) The positions of the groups come from the order of enumeration, so the
  inverse recomputes the offsets of the groups. (3) A solver decision filters
  the tuples of child groups, so the inverse sums the sizes of the earlier
  accepted tuples. (4) About twenty construction sites in the joins, chains,
  grouped and bucket layers, and six places in `compile`, would change, and the
  extra field would cost on the path of the LTA cells.
- An index of all the members, built once from `Gen.values`: works for a small
  generator only, and lists the members.

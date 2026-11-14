# 7. Opt-in invertible blocks give term-to-rank for combinator generators

## Context

The Index goal says that rank and term are inverse maps. `Gen.unrank` decodes a
rank. An automaton import has the other map, `Gen.rankOfTerm`, because its
engine term is the accepted user term. A generator built from combinators
(`elements`, `node`, `oneof`, `<*>`, `fmap`) has no such map. Its engine term
holds the structure of the combinators: the choice index, the applicative
spine, and, after `Gen.Refinement.compile`, the refinement label and the keyed
joins that the symbolic count needs. A user term has none of these. The
applicative `<*>` cannot give an inverse either, because its left side is a
language of functions.

## Decision

A block can carry the inverse of its values: `OutcomeIndex` has a field
`outcomeRankOfValue`. The blocks that have one are `invertible` (a source with
an inverse), `invertibleMap`, `invertiblePair`, the choices (`oneof`,
`frequency`), `pay`, `node`, and `atomic`. `rankOfInvertible` reads it for a
finite generator. A plain `fmap` has no inverse, and the generator then has
none. This is opt-in: a user builds the generator from these blocks.

Automaton imports keep their own route, `rankOfTerm`. The next step
propagates the inverse through `compile`, with `Lattice.pointRank` as the
inverse of the integers of a symbolic leaf.

## Why

- A compiled engine term cannot be the user term, because the count needs its
  extra structure. An inverse at the value level does not touch that
  structure.
- The inverse of a product is the product of the inverses, and the inverse of
  a choice is the union of the inverses of its alternatives, moved by the
  offsets. So the blocks compose, and no search is needed.
- The cost is a field. The inverse is a thunk that nothing forces unless a
  user asks for a rank.

## Consequences

- Every `OutcomeIndex` has one more field. `frequencyStatic` builds one more
  thunk. On the eight standard cells the allocation changes by at most +0.09% (`lta-do 20`), and the checksums are equal.
- A value that appears in two alternatives of a `oneof` has two ranks, as
  `oneof` counts it twice. `rankOfInvertible` gives all of them.
- A generator built with `<$>` and `<*>` has no `rankOfInvertible`. The user
  chooses the blocks.
- A compiled generator has no inverse until the next step. `rankOfInvertible`
  reports it.

## Discussion points

- Keep the user term as the support, as an automaton import does: rejected for
  combinators. It would remove the keys and the refinement labels of the
  engine term, and the symbolic count of `compile` depends on them.
- A search over the engine terms with `termAt` and `rankOf`: rejected. The
  rank order inside a size class has no key that a search can use, so the search
  lists the members.
- An index of all the members, built once from `Gen.values`: works for a small
  generator only, and lists the members.

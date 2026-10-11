# Distinct term indexing

`MicroCFTA.DistinctRank` separates accepting runs, distinct terms, and weighted
generator members. `bounded` removes repeated terms from `Language.enumerate`.
Its `Index` stores each accepted term exactly once. `decode_encode`,
`encode_decode`, `decode_injective`, and `unique_rank` prove the bijection with
`Fin count`. `finiteLanguage` indexes the entire accepted language when the
supplied height bound contains every accepted term. It states that coverage
condition explicitly.

`count_eq`, `decode_translate`, and `translate_roundtrip` show that two complete
indices of the same language have equal cardinalities and inverse rank
translations. They allow an optimization to change the enumeration order.
They do not prove that any Haskell optimization preserves the language.

`rankDistribution_event` preserves every event mass when weighted members map
to distinct ranks. `rankMass_eq` identifies the mass at a rank with the sum of
the masses of its decoded term. Uniform distinct-term sampling assigns `1/n`
to each term. Uniform accepting-run sampling need not do this: the checked
example `[0, 0, 1]` assigns `2/3` to zero before duplicate removal and `1/2`
after it. Duplicate removal alone therefore does not preserve a distribution.

The reference index materializes the language. It gives no efficiency bound.
Its rank order retains the last occurrence and is not the Haskell constructor
order. The file does not prove that the Haskell symbolic compiler refines it.

## Source comparison at `tidy/core-formula`

`Data.CFTA.Gen.fromAutomaton` promises distinct terms for acyclic automata.
`Gen.Internal.Automaton.compileFiniteAutomaton` chooses a compact plan for
disjoint alternatives and uses `Gen.Internal.Symbolic.symbolicRanked` for
overlap and deep equality. The symbolic counter uses inclusion-exclusion.
Cyclic imports reject ambiguity and equality constraints. This is an explicit
restriction of the implementation's supported language class.

Ordinary generator combinators have member ranks. They can give multiple ranks
to one term after `node` removes private choice labels. This is documented in
`Gen.Internal.Query.ranksOf`. It differs from distinct-term indexing and is not
a new implementation defect.

A focused executable probe ran in `nix-shell` after the rebase. It checked:

- `f({a,b}) | f({b,c})`: cardinality 3, outputs `f(a), f(b), f(c)`, inverse ranks
  `0,1,2`.
- `pair({a,b},{a,b})` with equal children, union `pair({a},{a,b})`: cardinality
  3, outputs `pair(a,a), pair(a,b), pair(b,b)`, inverse ranks `0,1,2`.
- `node "x" (oneof [pure 7, pure 7])`: cardinality 2, equal terms at ranks 0
  and 1, `ranksOf` returns both ranks, and the value PMF is `(7,1)`.
- Importing that generator's support with `fromAutomaton` gives cardinality 1.

These checks confirm the API distinction on the stated examples. They do not
prove general correctness of either compiler. The temporary probe is
`/tmp/microcfta-distinct-ranks.hs`; no regression test was added.

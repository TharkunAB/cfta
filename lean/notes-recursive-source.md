# Recursive source records

`SourceMinimum.lean` computes minimum metadata for the finite source algebra.
`member_bound` proves that each size-class member has a finite computed minimum
at or below its size. `none_is_empty` derives class emptiness from absent metadata.

`RecursiveSource.lean` connects a typed recursive body to the separate count,
decoder, and sampler fields. Its body constructors are closed finite sources,
the recursive occurrence, maps, pays, equal-weight choices, and products.
Closed sources retain `FiniteSource` atomic and weighted source behavior.
The recursive choice uses the public count policy. The product includes every
split from zero through the requested size.

The proofs establish these properties:

- `assumption_fixed` derives the minimum fixed point from the source probe.
- `derives_minimum` gives a minimum bound for independent finite derivations.
- `values_complete` proves that the source size guard permits smaller-size
  recursion. A product can guard an occurrence through a positive-size sibling.
- `family_exact` equates each compiled class with independent finite derivations.
- `family_live` proves normalized live mass, positive coverage of each valid
  member rank, and replay of every sampled rank through the decoder.
- `family_values` and `family_count` prove the exact ordered member stream and
  count. Repeated values remain separate members.
- `family_probability` equates sampler fields with a separate probability
  recurrence. Closed atomic weights persist through recursive products.
- `bounded_exact`, `bounded_sample_exact`, and `bounded_probability` compose
  all classes below a bound. They retain each admitted derivation and its mass.

The model follows `Gen.Internal.Recur.recur`, `Ranked.Internal.Size` class
operations, and `Ranked.Internal.Sampler` count-weighted choices. It computes
the recursive class record rather than assuming that record is correct.
`OccurrenceGuard.lean` separately checks the additional term-growth guard.
The completeness theorem requires the computed size guard to accept the body.
It does not treat an arbitrary recursive Haskell function as this typed syntax.

This theorem covers one recursive knot with a finite typed body. It does not
yet derive nested or key-indexed recursive body translation, fresh-token
allocation, GHC evaluation of the lazy knot, machine-integer selection, or
support and term-view callback correspondence. Those are source adapter and
runtime obligations. A class can contain repeated values or terms. A distinct
term rank theorem requires a term-uniqueness proof in addition to this member
record theorem.

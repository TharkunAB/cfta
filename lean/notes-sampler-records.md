# Decoder and sampler record invariants

`SamplerReplay.lean` connects independently constructed decoder plans and
exact value/rank sampler fields. `Coherent` states that both sampler fields
have the same output distribution and that every sampled rank decodes to
its sampled value. `Covers` states that every valid decoder rank has positive
sampled mass. `Valid` also requires normalized probability in both sampler
fields. `LiveValid` permits empty classes and requires normalization for
every class whose derived count is positive.

The executable constructors include weighted sources, map, products, binary
choice, the source's complete n-way `choiceParts` worker, and bounded size
families. Source ranks preserve input occurrences. Product sampler radices
come from their decoder counts. `choiceParts_replay` proves that skipped
empty alternatives retain the correct structural offsets. `many_covers`
proves that positive live alternatives cover every structural rank.
`bounded_decode` connects actual `boundedSampler` rank order to the checked
`PlanVariants.sized` decoder. `bounded_count` derives the sum of class counts.
`bounded_live` combines probability, replay, and complete positive coverage.

`FiniteSource.lean` derives these invariants for a typed source algebra.
It has sources, pure, map, pay, atomic, shared, weighted choices, products,
and bounded sized sources. It constructs whole-language and exact-size
records separately. Pure has size zero. A source has size one. Products use
every split from zero through the requested size. A pay shifts sizes by one.
Atomic boundaries keep their whole finite distribution at size one.
Ordinary finite branch weights become member counts inside size classes.
Atomic component distributions remain intact.

`finite_members` and `class_members` compare the executable records with
independent member-list semantics. `finite_distribution`,
`class_distribution`, and `bounded_distribution` compare them with independent
probability semantics. `finite_live`, `class_live`, and `bounded_source_live`
derive the full record invariant by source construction. The theorems do not
assume that the completed source or compiler has the desired distribution.
Input positivity is the condition checked by the public weighting API.
`bounded_member_exact` proves positive sampling of every bounded member and
exclusion of all other members.

`RecursiveRecord.lean` connects actual recursive automaton class compilation
to these record invariants. `uniformRecord` samples ranks with the source's
cached decoder and derived count. `uniform_coherent` and `uniform_covers`
prove that no draw uses the fallback for an invalid rank and that every valid
rank can occur. `uniform_values` derives uniform probability over member
positions. `classRecord` uses the normalized `RecursiveSize.compileAt` plan.
Thus `class_live` needs no assumed exact-size record invariant.
`bounded_sample_exact` proves that the compile/class/bound/sample composition
returns all and only the accepted bounded complete terms of a plain cyclic
automaton. Ambiguous runs remain separate ranks. A distinct-term claim also
requires the unambiguity condition enforced by the cyclic import API.
`bounded_distribution` proves that actual size-count weighting of the cached
class samplers is uniform over the full bounded run range.
`bounded_event_probability` gives the exact event count divided by total count.

These are executable mathematical source models. The finite source algebra
does not represent every Haskell `Static` field: interned support construction,
term-view inverse callbacks, root-count inspection metadata, sharing keys,
and heterogeneous recipe reconstruction remain separate source connections.
The recursive result covers plain automaton imports. Arbitrary user recursive
fixed points and family knot productivity require the recursive occurrence
invariants. Backend probability laws, Haskell callbacks, and array/cached
representation correspondence remain explicit boundaries. The pure proofs
do not certify IO randomness or an arbitrary user-supplied callback.

Validation: the pinned Lean toolchain builds `MassRetention`, `SamplerReplay`,
`FiniteSource`, and `RecursiveRecord` with no `sorry` or additional axioms.

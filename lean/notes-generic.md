# Datatype grammar discovery and codecs

`Generic.lean` models the source `deriveFTAWithGrowthLimit` worklist. It checks
whether a type was already allocated before it checks growth. It reports a
missing atomic domain and a domain supplied for an algebraic type separately.
It allocates each new row before it visits the row's fields, in source order.
`growthPairs` uses the same nearest-ancestor type-constructor chain and counts
strict size increases. `growthError` reports the first increasing pair when
the count exceeds the supplied limit.

The driver uses an explicit finite set of descriptor states. The proof of
termination decreases the number of unvisited states or the pending task list.
`discover_correct` proves that every allocated row is the declared row, each
state is allocated once, and every requested state and field is covered.
`discovery_acceptance` proves exact preservation of the whole root language
when the finite descriptor set is complete. Cycles in that finite graph are
allowed. The result is an ordinary `Language.Automaton`, so its enumeration,
intersection, and distinct-rank theorems apply directly.

The finite descriptor set is a representation premise. The Haskell source
discovers `TypeRep` values dynamically. The proof does not establish that the
growth-limit policy rejects every infinite family of type representations.
It does model that policy and its failures. The source's `GHC.Generics` methods,
constructor metadata, `Show`/`Read` literal labels, and final `mkFTA` rankedness
validation still require correspondence. The model does not turn missing or
rejected types into successful empty grammars. An explicit empty atomic domain
is separately proved valid. Negative growth limits retain the source's
nonempty-increasing-pair condition.

`unknownNames_exact` and `checkAnnotations_exact` prove that an unknown
constructor annotation produces an error. A misspelled name cannot silently
receive the default annotation.

`Codec` states the legitimate user-codec requirements: every admitted term
decodes, and encoding a decoded value recovers that term. `codec_rank_total`
gives a decoded value for every admitted term rank. `codec_rank_injective`
derives injective value decoding from the round-trip requirement; it does not
assume that an arbitrary value map is injective. Without that requirement,
distinct term ranks can decode to equal values.

`checkCodec` models the source's finite constructor probes and preserves a
failed constructor label. `checkCodec_exact` proves exactly what successful
probes establish. `finite_probes_do_not_prove_codec_totality` demonstrates why
probing one term does not prove totality on other terms. The full codec law is
the caller's contract; the source does not exhaust the grammar to check it.

## Templates

`Template.lean` models all five constructors in `Data.CFTA.Template`.
`childTemplates_length` proves exact child alignment, including prefix padding
with holes. `matchesTerm_correct` connects executable matching to the complete
term relation. `restrict` constructs state/template pairs, retains source
guards, and changes only child destinations. `restrict_exact` proves that the
result accepts exactly the source terms that match the template. This proof
permits cyclic source graphs. `restrict_hole` proves the source hole shortcut.
The concrete interned binder representation and the `Map` construction in
`restrictFTA` remain adapters to this explicit-state algorithm.

## Source comparison

A focused Haskell probe ran in `nix-shell` after the rebase onto `d7f7c11`.
It confirmed missing-domain, non-atomic-domain, zero-limit type-growth, and
unknown-constructor errors. It confirmed that an explicit empty atomic domain
constructs a grammar and that a recursive datatype value round-trips through
the generic codec. Nine template patterns produced exactly the concrete terms
selected by `matchesTemplate`. The temporary probe is
`/tmp/microcfta-generic-template.hs`; no regression test was added.

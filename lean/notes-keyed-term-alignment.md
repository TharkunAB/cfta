# Typed keyed term and probability alignment

`KeyedTermAlignment`, `KeyedTermMass`, and `KeyedSamplerUnfolding` connect the
independent value, term, minimum, mass, and sampling fields of a finite
mutually recursive key family. They extend the existing `KeyedSource` model.

## Constructed fields

A body has correlated finite leaves, retained finite leaves, keyed
occurrences, maps, pays, binary choices, typed application, and user labels.
Application supports different intermediate Haskell value types. Every key
has the same root value type, as in `recurGrouped`.

The three interpretations build the fields independently:

- `valueRecipe` keeps the actual values.
- `termRecipe` keeps private application and choice terms and user labels.
- `pairedRecipe` keeps each value with its corresponding complete term.

`sourceWrap`, `sourceTermProgram`, and `sourcePairedProgram` use the actual
`Recur.hs` member constructor:

```
AtKey [Key position [], Family [Key position [], body]]
```

Each recursive occurrence uses its own key's wrapped body. This is not the
single-root `Recursion` wrapper. `position` is the index in the complete
settled `Map.keys keyMinimums` order, before productive keys are filtered.
It can have gaps after that filter. `KeyedTermCodes` proves the source
key-position map and its injectivity. Forward alignment does not need an
injectivity assumption about the wrapper.

`body_values`, `body_terms`, `family_values`, and `family_terms` prove exact
ordered projections. `class_counts`, `decode_value`, `decode_term`, and
`rank_alignment` prove that each key has the same counted interval in the
paired, value, and term indexes. They retain duplicate values. Bounded
projections retain the complete size-major prefix and the same class offsets.

`minimum_expressions`, `minimum_programs`, and `minima_equal` derive the same
key-presence and minimum-size metadata for all interpretations. The source
value guard implies both term guards, including cross-key positive-sibling
product guards. `paired_exact` gives all-and-only finite typed derivations.
`live_keys_exact` proves that the minimum filter keeps exactly the keys with
a nonempty term class.

## Weights and the full knot

`SameGroup` compares the unnormalized key mass, structural count, and complete
ordered rank probability law. Maps preserve them. Products multiply key
masses and combine ranks with the source mixed radix. Same-key merges choose
by key mass while offsets still use member counts. Retained source weights
remain nonuniform. `retainedLive` accepts sparse mass functions that are
positive only at live sizes; an unused empty-class mass does not affect any
field.

`GroupedMergeAssociativity` proves exact equivalence between a flat merge
and a merge whose suffix is grouped. Counts determine the rank offsets.
Key masses determine the probabilities. The theorem preserves the ordered
decoder members and complete rank/value/mass runs. Empty and singleton
classes retain their correct behavior. This is a local source-field theorem;
the flat n-ary body adapter must still instantiate it.

`KeyedTermMass.family_values` and `family_terms` derive this relation at every
key and size. `ranked_values` and `ranked_terms` then prove equality of the
full rank/value/mass and rank/term/mass distributions. The bounded results
preserve those laws under count-weighted size selection. The source stores
one value sampler and an independent term index. The term interpretation's
sampler is a mathematical comparison of the mass assigned to each term
position, not a claim that Haskell stores a second sampler in `RecursiveTerms`.

The executable family uses a smaller-size cutoff for termination.
`KeyedSamplerUnfolding` proves that each accepted class also satisfies the
full simultaneous source equation. An empty grouped sibling has zero key
mass and no sampler ranks. It therefore removes both the mass and sampler
of an unmatched current-size product component. Together with
`KeyedSourceUnfolding`, this proves the complete count, key-mass, ranked
sampler, and value-sampler equations without assuming a correct whole-family
knot.

Kernel examples use two mutually recursive keys. They check the exact
`AtKey`/`Family` term after a cross-key occurrence, retain equal user values
at separate ranks, and preserve a 9:1 retained mass ratio after two mutual
steps.

A temporary Haskell comparison used two keys, four weighted operations,
and two base leaves. An independent exact-rational tree recurrence checked
all eight size classes. It checked normalized public key masses, conditional
within-key probabilities, and every one of the 254 bounded and unbounded
term-rank inverses. Every decoded term was accepted by the source support.
This check passed on `bbeb7be` with the local repairs. Public `massesAtSize`
normalizes the stored positive key masses across the current class. The
proof's `SameGroup` relation preserves their unnormalized scale as well.

## Source error order and scope

`Recur.recurGrouped` has these source decisions:

1. A failed probe returns its generator error first.
2. A successful probe with no occurrence returns `probeBody` directly.
3. In the recursive path, a failed build around `samplingPlaceholders`
   returns its error. The probe result is then read again.
4. An unguarded occurrence returns `UnguardedRecursion`.
5. No finite minimum returns `EmptyGenerator`.
6. The result keeps only settled keys present in the built bodies and in
   the finite-minimum map.

The modules cover the successful guarded path after a finite key set settles.
The key type represents that finite domain. The existing `GroupedProbe`,
`GroupedMinimum`, `GroupedFlags`, and `GroupedChoice` modules cover their
stated discovery, flag, and choice rules. The new proofs do not change the
source error precedence or reinterpret an error as an empty success.

The source evaluates `bodyGroups` in several placeholder contexts. These
include index, mass, sampler, term, metadata, and support builds. Some
intermediate builds map errors to empty maps. The public recursive result
checks the final body and probe errors, and it installs a term callback only
when that key exists in `bodyTerms`. The formal family uses one fixed typed
constructor schema in all these interpretations. It does not prove that an
arbitrary Haskell builder preserves its schema, key set, and errors across
those contexts. In particular, a successful value generator with no term
callback is outside the total-inspection theorem.

Flat arbitrary-arity choices, recursive grouped joins, key regrouping whose
shape changes between placeholder builds, nested runtime family schemas,
and lazy Haskell productivity need their own source adapters. The modeled
application uses the ordinary `Recursive.productTerms` `Apply` constructor.
`Grouped.applyRecursive` instead uses `recursiveJoin` and `Chain`, with
`JoinN`, `CenterKeyed`, `ArgKeyed`, and component tags. Equal count and mass
product formulas do not identify those different private term structures. Binary typed choices here keep
the source's two branch labels; they do not claim to represent a flat n-way
choice by inserting extra binary term wrappers. Unbounded key creation is
the source's documented nontermination boundary. Solver, callback, container,
and runtime contracts remain separate. A bijection on distinct terms still
needs the independent term-injectivity condition.

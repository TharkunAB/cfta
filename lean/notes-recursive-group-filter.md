# Recursive group key filtering

The repaired recursive branch of `Grouped.filterGroupsM` traverses
`Map.toAscList groups` with `filterM` in `ExceptT`. It applies the predicate
to each key. It rebuilds the retained map with `Map.fromAscList` and keeps
each complete `KeyedRecursive` value. It does not enumerate members or
retie the recursive family.

`RecursiveGroupFilter.run` executes that filter with an explicit predicate
effect state and callback trace. `calls_prefix` proves that executed calls
form an initial segment of the input key order. `successful_calls` proves
that success visits every key. `failed_calls` proves that the first callback
error is the last call and that every earlier callback returned a Boolean.
`calls_unique` proves at-most-once calls for unique map keys.

`retained_sublist` derives complete-record retention from the executable
filter. `retained_order` preserves the ascending-key relation needed by
`Map.fromAscList`. `retained_exact` and `lookup_retained` prove exact key
selection and map readback. `effects_key_only` proves that replacing every
opaque record cannot change the callback trace or final predicate state.
The filter does not inspect any record field.

`filterRecursive` models the source error layers. A stored generator error
stays inside the recursive family and causes no callbacks. A predicate
error remains an outer error. A successful empty map remains a successful
recursive family. `recursive_keys_exact` connects this complete wrapper to
the exact retained-key theorem.

The semantic instantiation uses the existing `KeyedSource.family` class
records. `keyed_record_retained` proves equality with the original tied
class function. `keyed_fields` derives exact per-size counts and decoder
replay, sampler equality, unchanged class masses, and unchanged metadata.
`keyed_metadata` preserves every metadata observation, including minimum,
support, term indexes, inspection, and both weight flags. It does not assert
that filtering preserves the relative selection probabilities of the whole
family; later selection can normalize the retained groups.

`keyed_language` retains the independent finite-derivation semantics of the
original recursive program. Internal references to a key remain available
even if that key is absent from the filtered public map. No theorem assumes
a desired whole-filter preservation law. No retained mass is recomputed or
normalized by this filter.

## Remaining interfaces

The input list represents the source ascending map traversal. The theorems
preserve its order and unique keys. Host `Map` representation and its
`Ord` instance remain interfaces. The explicit predicate transition models
observed key-level effects; it does not prove arbitrary IO callbacks or
handle exceptions outside their returned `Either` values.

Whole-record equality preserves metadata without interpreting it. The
source correspondence of individual support, index, and inspection fields
remains covered by their own adapters. The unchanged finite filtering
branch is outside this new module.

## Validation

`lake build MicroCFTA.RecursiveGroupFilter` checks 20 theorems and 61
dependency modules. Principal declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

The source repair passed 613 examples: 281 core, 194 generator, and 138
refinement examples. Focused filtering and recursive refinement checks also
passed. Fourmolu, cabal-gild, and whitespace checks passed. The retained
source probe is [RecursiveGroupFilter.hs](repro/RecursiveGroupFilter.hs).
For a productive Mu, its size counts are `[0,1,1,1,1]`; for `Mu | b`, they
are `[0,2,1,1,1]`. The probe also checks wrapper pay shifts and bounded values.

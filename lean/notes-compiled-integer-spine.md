# Concrete keyed integer-spine terms and ranks

`CompiledIntegerSpine` follows the one-group fragment of
`Compile.compileOpenSpine`. Its syntax is pure values, integer domains, maps,
pays, and applicative products. `compile` retains lattice errors and empty
groups. Each successful node returns one key list and one original static
outcome. This is the internal open-spine path. A public generator with no
integer leaf can instead take `compileGen`; that dispatch is not replaced by
this model.

The source wrapper path is concrete:

- `keyed` stores the original static payload in a singleton map.
- The integer fallback uses `regroupOn pure`. Its single bucket takes the
  `mergeBucketGroup [bucket]` positive-mass fast path.
- `relateGroupsM` has one accepted key pair in this fragment. Its component
  index is zero. `pairBucket` calls `joinNBucketStatic` with a size-zero Pure
  operation and the function and argument statics, in that order.
- The selected term is JoinN. Its first child is CenterKeyed with the Pure
  operation and the two ArgKey leaves. Each remaining child is ArgKeyed with
  its corresponding key and complete argument term.
- `mergeComponentsByKey` normalizes the single bucket mass and retains its
  static payload through the same singleton fast path. Mapping the reader,
  paying, `joinPositioned`, `atKey`, and singleton `ungroup` retain that term.
  No Group, Choice, AtKey, or Family wrapper is inserted on this path.

These source facts define `template`, `compile`, and the recursive candidate
callbacks. The map representation itself is projected to its singleton
payload. General multi-key merging is not part of this fragment. `groupOn`
is not used by these integer/pure constructors; arbitrary closed components
that require it remain outside this proof.

`template_valid` proves every Pure and Placeholder is nullary.
`template_count` derives that the private keys consume no coordinates.
`compile_exact` proves that the concrete term construction agrees with the
source key and error traversal in `OpenIntegerSource`. `compile_dimension`
derives the final hole count from the constructed keys.

`pairChildren` and `pairCandidates` use the actual join and chain callback
shape. Every operand has one original outcome, so each original radix is
one. The key checks contribute CheckedRank flags, which `pointsStatic`
intentionally ignores before its final exact view check. `candidate_complete`
proves discovery recursively through nested keyed joins, not just through
ordinary Apply terms. Filling preserves every private key and consumes the
function coordinates before the argument coordinates.

`compiled_ranks_exact` connects the concrete template and candidate callback
to the actual integer singleton reader, public lattice table, tuple ranker,
and final `hasView` check. It covers WholeTerm, SpineView, and LabelledView.
`compiled_decode_injective` proves that every valid integer rank has a
distinct projected term. All template shape, hole count, and candidate
coverage premises are derived from the generated recipe. The public closure
table must successfully compile its generated formula. The theorem does not
claim that the lattice compiler accepts every finite mathematical domain.
For a zero-width group, the source uses its direct reader application branch;
the shared closed-table theorem characterizes the equivalent tuple-indexed
view, rather than asserting that the source makes a redundant lattice call.

`OpenIntegerReaders.template`, `IntegerTermViews.template`, and
`OpenIntegerSource.source` remain ordinary Apply reference structures. Their
coordinate, value, and local codec theorems are valid, but they are not the
keyed output of the grouped compiler. Their comments and notes now state this
distinction. This module supplies the concrete adapter for the stated
one-group fragment.

`lean/repro/IntegerSpineTerms.hs` checks the public implementation independently.
It compares complete private terms, all key indexes, all singleton integer
refinements, and inverse ranks. The mapped pair and nested lifted pair have
nine outcomes each. The nested identity and mapped integer have three each.
All 24 comparisons pass in the project Nix environment. This is conformance
evidence, not extraction of Haskell definitions into Lean.

Remaining paths include multiple observation groups, arbitrary-length
weighted choices, computed constructor labels, complete parent settlement,
and recursive imports. Their local callback and metadata laws remain in
separate modules. This result does not turn repeated user values into distinct
values and makes no new claim about sampling weights.

Validation: the pinned Lean 4.34.1 build passes. The retained Haskell probe
passes after Fourmolu formatting. No production Haskell source changed.

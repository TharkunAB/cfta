# Positive accessor boundary review

The checked theorem is `SourceCurrentPositiveAccessorBoundary.live_pair_lost`.
The first stored field is empty. Its guard is `Same [0] [1]`. Its actual
accessor returns the live class `[[[0],[1]]]`. The second stored field is
empty. Its guard is `Not Bottom`. The positive parser does not support this
guard. The actual conjunction keeps both guard atoms and the empty stored
field. The joined positive parser returns outer `none`. The joined accessor
returns `some []`. It does not cover the first accessor class. Both actual
arity-two acceptance checks return true.

This is a parser boundary on complete constraint fields. The proof uses the
actual conjunction, staged positive parser, compact equality normalizer and
source constructor acceptance test. It does not construct a native execution
or establish a Haskell defect. It does not establish a renewal bound or
exclude an active owner collision. The outer `none` means unsupported syntax.
It does not mean `some none`, which means contradictory positive equalities.

The new source has one public theorem. Its exact statement aliases a private
checked witness. The kernel checks that both types agree. The full public
probe prints its statement, proof and axioms. Only `propext`,
`Classical.choice` and `Quot.sound` occur. There is no extra constructed or
auxiliary declaration count for the same witness.

`guard-direct-2` passed with a zero-byte log. `guard-canonical-1` completed
all 1050 jobs. It replayed only the existing unused-variable warning in
`InternedFreshOrdinaryClosedCompletion.lean:24:5`. The new source has no
warning. `guard-public-1` passed all eight printer settings and the full
proof/axiom checks. Each process ran with memory.max and memory.high equal
to 4294967296, memory.swap.max equal to zero, and a five-minute limit.
`guard-direct-1` remains as an unselected failed snapshot. It failed on two
missing application parentheses in the Covers statement. It proves no
separate mathematical boundary.

The planned positive coverage module was not written. Existing
`SourceCurrentPositiveClassOrigins.normalized_guard` and `source_guard`
already prove the two proposed coverage endpoints. Existing `field_split`
and `key_ne_top` supply the actual inherited child and key consequences.
The earlier search missed this module because it searched proposed theorem
names and the semantic parser endpoint instead of the positive-origin
module names. This package adds the live-pair loss witness instead.

## Supported joined guards

The following route is a source review, not a new checked theorem.
`GuardConjunction.merge_mem` preserves exactly the outer atoms of both
operands. `SourceCompactGuards.positive` supports only Top, nonreflexive Same,
and conjunctions of supported guards. Thus successful extraction from the
joined guard rules out an unsupported atom in either operand. Each raw pair
emitted by either operand remains a pair emitted by the joined traversal.
Sorting and duplicate removal can change order and multiplicity, but they
do not remove pair membership. For a live joined accessor,
`SourceCurrentPositiveClassOrigins.source_guard` then covers those raw pairs
in the joined effective output.

This route concerns raw positive pairs. It does not by itself prove that
an entire separately normalized operand component occurs in one joined
component. That stronger endpoint needs a connected-component transport
argument. It must also cover stored classes. The existing
`SourceCurrentOwnClassOrigin.effective_covers` handles raw stored classes.
No unconditional operand effective-coverage theorem is valid when joined
positive extraction is unsupported. The checked witness proves that limit.

## Reviewed source pins

| Path | SHA256 |
| --- | --- |
| `lean/MicroCFTA/SourceCurrentPositiveClassOrigins.lean` | `cc80873c0fed4cd948e941b56f161dd28b9fa7f6eea08037963733c54e4996d4` |
| `lean/MicroCFTA/SourceCurrentNativeOwnOriginBoundary.lean` | `29faf76482075c49d8a3634c2ed0ec922f2e8a8d33c97b58f78971d2623e66d8` |
| `lean/MicroCFTA/GuardConjunction.lean` | `a9eed3a6530af04282836dcefdb628e578aed27a5b4d9789ec9da5b9b40c790c` |
| `lean/MicroCFTA/SourceCompactGuards.lean` | `f325f71a99c33a2d966cd5a8caebb2924d91b0df612936e0e86d9c8aba5b4d60` |
| `lean/MicroCFTA/SourceEqualityMkEdgeAllocation.lean` | `5365ae3e5a39760b9052aef795c9eb609fb726516960fc48f5ef55367e41236a` |
| `lean/MicroCFTA/SourceEqualityConstraintConstructors.lean` | `4ee4347bb18b296b0dd6eb289b364c2e19fffdde98c625dbad3a2513462e4fe9` |

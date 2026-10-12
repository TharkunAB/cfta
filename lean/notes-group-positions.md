# Complete group position tables

`GroupPositions` models `firstPositions` as the actual left-to-right map
insertion with the earlier value retained. `build_lookup` proves that this
fold equals an independent first-occurrence search. Duplicate identities
retain their first position. Every stored position is in the zipped range.

`regroup_lookup` derives a successful position lookup for every entry that
`regroupOn` receives. It applies to finite and recursive group records. The
finite key map exists even when the member language has no finite
cardinality. The proof uses the actual `groupKeys` projection from either
source constructor. It needs no member-count assumption.

The previous open helpers used `cardinalities` to discover their keys.
That operation returns `UnboundedGenerator` for a successful recursive map.
The helpers converted the failure to an empty key list. Their later partial
map lookup then had no entry. `old_recursive_counterexample` proves this
failure with one recursive group.

The public reproduction mixes a productive recursive import with a bounded
integer generator. A parent constructor forces the group's keys. Both
`uniformly` and `oneof` raised `Map.!`. The repaired `repositionOpen` and
`joinPositioned` use `groupKeys`, as the closed `reposition` already does.
The open closure still reports its existing `UnboundedGenerator` error.
The repair does not claim support for recursive symbolic integer closure.

`position_machine` connects the natural position to the signed word model
when the key-list length fits the source position range. The physical Map
representation and that host-size bound remain explicit interfaces.

The positioning proof guarantees complete lookups and first-position
retention. Bucket merge semantics use the separate grouping and mass
proofs. Concrete heterogeneous callback composition remains a separate
obligation.

Validation on 2026-10-12: the pinned Lean module build passes. The retained
public reproduction passes. All three existing Nix test suites pass:
282 core, 194 generator, and 142 refinement examples (618 total).
Fourmolu and the affected package's cabal-gild check pass.

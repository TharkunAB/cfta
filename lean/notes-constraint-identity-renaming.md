# Physical constraint identities across allocation histories

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
This extends [completed result-memo soundness](notes-result-memo-soundness.md).
The production Haskell code is unchanged.

## Source allocation boundary

`Equality/Constraint.hs:179-214,265-314` interns the ordered class list.
Each class compares its structural trie. Its lazy path-set and cached-hash
fields do not participate in equality. The source `IntMap` representation
requires ascending child entries and representable machine child indexes.
The smart constructors derive coherent metadata and hash fields.
Live equality constraints compare and hash their strict signed `Int` identity.
Contradiction has a separate tag. Live empty constraints have a canonical
allocated identity, which need not be zero.

The source equality cache is process-global. Construction can allocate entries
before partial reduction starts. The following sites can reach more interner
requests. Lazy demand and short circuits determine which requests execute.

| Site | Source |
| --- | --- |
| Positive Same guards, intermediate And guards, and stored/guard combination | `cfta/src/Data/CFTA/Constraint.hs:129,171` |
| Contradiction precheck and selected endpoint intersection | `cfta/src/Data/CFTA/Equality/Operations.hs:185` |
| Native edge conjunction and mkEdge arity checks | `cfta/src/Data/CFTA/Interned/Operations.hs:358,529`; `Interned/Type.hs:563` |
| Inherited/local combination before child processing | `cfta/src/Data/CFTA/Equality/Operations.hs:92`; `Equality/Constraint.hs:449` |
| Empty, singleton, or sorted descended payload construction | `cfta/src/Data/CFTA/Equality/Constraint.hs:467` |

The model's `prepare` names request-observed physical keys in a fresh table.
Its native prefixes and pure payload helpers do not record all the events
above. Numeric counter equality and full constraint-table equality would be
incorrect correspondence requirements. Production combination and descent
also have separate global memo tables. Their exact event schedule is not
part of the current result-worker state.

## Stable canonical identity correspondence

`CacheRenaming.Covers` permits extra keys in the second interner.
`Linked` relates two stored canonical identities through one complete key.
Valid tables derive equality preservation in both directions. The relation
is functional and injective on these stored identities. It makes no claim
about unused reserved candidates.

Shared-key interning derives related returned identities and retains coverage.
Old pairs survive independent table growth and arbitrary permitted atomic
`Cache.Steps`. The two supplies can have different counters and reservation
histories. Existing first-writer cache invariants retain losing candidates.

`SourceEqualityPartialConstraintRenaming` preserves contradiction separately
from live payloads. Actual identification and request preparation derive
related identities and complete result-memo keys. Recorded identity transport
retains the original ordered physical payload. Coherent inherited records
then derive equal satisfaction. Complete key equality remains equivalent in
both directions, including the unchanged node reference component.

## Result-memo publication and semantic provenance

`SourceEqualityPartialMemoRenaming.Related` relates both publication tables
and the same logical cells and allocation count. Each published key has a
corresponding key at the same handle in the other table. Cells retain the
same complete original request, phase, and returned value.

Independent constraint table growth retains this relation. Related candidate
keys observe the same handle or miss. Actual `prepare_publish` preserves the
handle and both publication directions. Actual demand observes the same
absent, evaluate, busy, or ready branch. Phase updates and completion preserve
the relation and the stored original request.

The relation derives the second table's complete original-request validity.
`Related.sound` transports every completed-cell proof under actual native heap
preservation and valid second-side constraint storage. It requires no future
Sound premise. Native Scope and source allocation receipts remain separate.

This relation compares corresponding logical result-memo histories. It does
not allow arbitrary extra pre-existing result cells in the second table.
The actual process-global result memo needs a separate warm-history refinement.
Equal nonmemoized native effects are not assumed.

## Actual signed machine identities

`SourceEqualityPartialConstraintWords` connects recorded reservation ordinals
to `InternedIdentityWords.identity`. A valid interner and a complete supply
count within one word period derive equality equivalence for recorded tagged
identities and full memo keys. Physical renaming composes with this conversion.
Negative signed identities remain valid. The `bits` parameter counts magnitude
bits. A word with w total bits uses bits = w-1.

The bound counts every global reservation, including candidates that lose
insertion races. A bound on resident entries or current requests is insufficient.
The source counter has no overflow guard (`Interned/Cache.hs:83-91,169-177`).
Existing `full_wrap` and `not_unconditionally_fresh` retain the failure of
unlimited freshness. This checkpoint does not derive a process lifetime bound.

## Concrete prefix status

The [allocation receipt proof](notes-payload-allocation-receipts.md), `bb35a074`,
now derives actual completed combination/descent effects, guard/accessor demand,
and native precheck allocation receipts. These concrete prefixes preserve full
result-cell Sound. Full native conjunction/intersection, edge rebuilding, and
original graph-construction effects remain next. The section below records
the earlier general allocation-interface target.

## Next source obligations

Record actual allocation-capable payload and native-prefix receipts. Relate
each reached production entry to its represented ordered physical key. Apply
the proved correspondence at actual memo operations. Retain actual demand
and short-circuit behavior. Do not impose a textual allocation order.

The source hash/IntMap/cache library bridge, unsafe IO, atomic runtime adequacy,
machine index representation, complete lifetime reservation bound, and global
result-memo history remain open. This checkpoint proves the typed refinement
interface. It does not prove complete production runtime correspondence.
General caller completion, open contexts, repeated fixed points, getAllAtPath,
decision-model, named measures, parser/decoder bridges, and extraction remain
open. The earlier successful and busy fixtures remain preserved.

## Validation

Focused command:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityPartialMemoRenaming MicroCFTA.SourceEqualityPartialConstraintWords
```

This passes 1,046 jobs. Log: `/tmp/mcfta-memo-renaming-20261015.log`.
The full `lake -d lean build` passes 1,918 jobs and checks 49,920 theorem
dependencies. Only propext, Classical.choice, and Quot.sound occur.
Log: `/tmp/mcfta-constraint-renaming-audit-20261015.log`.
The existing unused-input warning remains. No new module has a warning.
No Haskell file changes. Earlier Haskell, Nix, format, and metadata checks
retain their prior source evidence and were not repeated.

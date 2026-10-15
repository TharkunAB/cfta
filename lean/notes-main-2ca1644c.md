# Main 2ca1644c: enumeration storage, order, and grouped exclusion

Source main is `2ca1644c908b41567e57f396c7e00befc692bae7`.
The preserving merge is `a7134ecb`. The previous source is `7fdebd07`.
Eight package files change. No source module is added. Full library scope
and the optimized interned core remain.

## Enumeration storage and order

The value slots change from Seq to strict IntMap. The initial map contains
the root UVar. Fresh allocation inserts at the current supply. Reads resolve
the union-find representative before slot lookup. Writes still use the raw
supplied UVar. Eliminated slots remain stored.

`SourceCurrentEnumerationStorage` models the finite-map lookup and insertion
interface. An exact allocated prefix relates the map to the earlier list
slots. Initialization, fresh insertion, and in-range writes derive this
correspondence. An out-of-range IntMap insertion adds a key. An earlier
out-of-range list update does not. The allocated-domain condition is required.
Actual bounded union-find reads retain their representative result.

One `_edgesOf` closure replaces separate canonical rows and edge weights.
`canonicalEdgesOf` captures the weighted original root map. A hit uses its
stored rows. A missing node uses that node's weighted canonical edges.
The weight sort remains stable and descending. Equal weights retain the
earlier edge order. Source documentation excludes NaN weights.

`runsInterned` uses raw nodeEdges order. It requires no symbol ordering.
Earlier process interning can change that order. Ordinary `runs` and
`runsBy` retain their canonical root-map and fallback path.

`SourceCurrentEnumerationOrder` derives the exact closure equations,
root-map hit and fallback behavior, stable weight-stage facts, and raw
ordinary/CPS branch order. Supplied rows are completed finite lists.
Actual canonical-class computation, Double ordering, physical IntMap/Seq
storage, machine UVar capacity, strict forcing, and whole scheduler
correspondence remain open. These adapters do not prove the entire current
enumerator or its representative waiting-count invariant.
The source sortOn and modeled mergeSort still need implementation
correspondence. Root-map NodeId coherence remains explicit.

## Grouped template exclusion

`exclude`, `refine`, and `edgeCopies` now require Ord symbols. `refine` uses
stable nubOrd. `edgeCopies` groups equal live ground parts and removes groups
that also occur among dying ground parts. It enumerates no matching ground
part or one admissible group. Open parts retain the subset split.

The recursive `ground` predicate accepts only finite TemplateNode trees.
Such a pattern has one structural term. The predicate is not an equivalence
test for every pattern that denotes a singleton.

The complete edgeCopies partition, group order, obligation normalization,
reachable closure, unambiguity, and cyclic/fromRows construction still need
source bridges. Existing template matching and matchesNowhere theorems
do not establish this construction.

## Other source boundaries

Derive.hs and its documentation remove the deriveNode TODO. They add no
deriveNode implementation or export. The typed NodeView/MeasureRecord
obligations remain as recorded in `notes-main-7fdebd07.md`.

Equality, gate/descendant workers, emptiness bodies, Interned native code,
Sized, and solver/refinement core are unchanged by this source delta.
The new regression tests are execution evidence. They do not discharge
the remaining source correspondence obligations.

## Validation and preservation

The required strict Nix build passes all components with `-Werror`.
All six suites pass 720 examples plus golden checks. Fourmolu passes all
five changed Haskell files. Cabal-gild passes all four active package files.
Logs and the exact source diff use `/tmp/mcfta-query-global-main-2ca-*`.

All package changes come from the preserving upstream merge. Existing
retained repairs remain. Earlier proof definitions, repros, marked drafts,
stashes, and other worktrees remain. HANDOFF.md records the closing audit
and preservation snapshot.

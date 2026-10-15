# Merge-result memo provenance and first-writer publication

`SourceCurrentMergeResultMemo` models the separate source
`genericMergeAlternativesCache`. The key is the tagged physical NodeRef.
A symbol type has its own source table. The three global unfolding/query
tables and native task tables are different caches.

## Completed results

A completed entry retains its original input record and literal result.
Correct requires exact keys, resident input and output, and a historical
actual completed producer. A cache hit returns that result and leaves the
whole native state and memo bundle unchanged. It does not execute the body
again. A miss uses the existing actual finite merge body and records its
returned result. `complete` branches on literal lookup. `verified` derives
actual global receipts, final three-table coherence, retained entries,
resident output, historical provenance, and unchanged native table domains.
The historical producer derives language coverage and closed output when
its original input was closed. Open inputs keep their complete records.

## Publication

The source installs a candidate thunk before it forces the merge body.
The independent Publication graph follows lookup, finite intervening inserts,
atomic keepFirst, more inserts, and the literal getD winner reread.
It derives first-writer retention, stored winner presence, captured key
coherence, and unchanged initial hits. The fallback is unused after the
insert. A candidate that loses publication need not run its body.

Publication is not completed-result insertion. No theorem yet connects the
published thunk to its completed producer or to GHC forcing. The current
Target OperandReads still calls the existing uncached body graph. Recursive
small-child and retained-union callbacks still use that graph. They have not
been replaced by memo-aware source requests. The completed projection and
publication proofs therefore do not close whole-source cache correspondence.

The next source proof needs mutually defined memo-aware request and body
graphs. Each recursive callback must use a literal lookup. A causal producer
history must derive the returned semantics and effects. It must not assume
that a hit replays the old producer in the current heap or that an uncached
body has identical state effects to a memo-aware body.

Source references: `Interned/Memo.hs` defines memoWith and the symbol-scoped
table. `Interned/Cache.hs` defines insertKeepingFirst and winner reread.
`Interned/Type.hs` defines NodeEqHash tag and reference identity. Focused
build, axiom probes, and publication examples are recorded in the checkpoint
snapshot under `mcfta-merge-result-memo-*`.

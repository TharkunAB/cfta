# Independent review of filtered publication reconstruction

Reviewed on 2026-10-18 at 01:14 CEST. No material issue found.
This review changes no production file and repeats no Lean execution.
It adds no proof declarations or probe pairs.

## Exact source and contract

- `SourceCurrentPublicationFilterSource`:
  `42fc591c24bd50f32209d284e1e539a45fdaaa47af92ad6a2f5fe4ec924372db`.
- `SourceCurrentPublicationFilterAlignment`:
  `d4cf0e581b01c472c88d8ddc2e60f5f5809796e24454aa93f1e1b784c03cb29a`.

The numbered final strict snapshots have these exact source hashes.
The public API contains six source definitions or theorems and two
alignment theorems. This review covers all eight.

`Publication` retains actual source syntax, fixed captures, three actual
callback equations, the exact missing key, and the reserved body call.
It is an actual-event receipt. This theorem does not construct an arbitrary
publication from an empty source heap. Initial data for the new producer
are that receipt, static `BinderFree`, `Keeps event.afterBody common`,
and an available replacement at `common`.

## Root erasure and exact parts

`rootErase` replaces the supplied `.var 0` with Empty only at the root
and through root union members. It leaves ordinary node child syntax,
guards, symbols, other captured variables, and binder syntax unchanged.
`rootErase_binder_free` proves that the transformation preserves the
static source restriction. `support_included` is a separate lexical
support inclusion law; it adds no name to that support.

The actual-call `source_parts` proof compares the original and erased
source builds at one common heap. It decomposes actual union builds into
ordered member calls and actual makeUnion effects. Actual validity,
growth, and replay remove intermediate heaps. It uses literal union
constructor laws rather than a semantic unfolding or desired result law.

The resulting `SameParts` statement uses complete Mu values as literal
atoms. It does not unfold a captured Mu to obtain an atom match. Ordinary
`Row` membership retains the complete `EdgeValue`: full guard, symbol,
and the ordered complete child list. Root row order and multiplicity
are deliberately not part of this membership relation.

`filtered_literal` handles bare self separately. The literal self-filter
retains a bare self result; the following `eraseSelf` removes it. The
combined operation removes exactly that reference atom from root union
parts. `filtered_row` preserves exact ordinary rows. It does not erase
matching references from ordinary children or from Mu bodies.

## Freshness and reconstruction schedules

The public `source_parts` has an explicit lexical freshness premise.
The publication producer discharges it from actual execution data.
`NativeNormalizationFreshness.ordinary` uses the actual Depth callback.
`reserved` uses the actual missing key and issued-name bounds. This is
freshness on live source support. It does not require the marker to be
absent from the entire capture list or from dead row syntax.

`warm_nonbare` obtains both original raw callbacks and their filters from
the actual event. It derives live lexical compatibility for the same
replacement. `StoredLiveUnionLineage.initial` constructs both erased
source builds and both erased stored reconstruction schedules. Their
actual Keeps receipts give the final Ready heap and persistent inputs.
Replay brings the old raw callbacks and the erased calls to that reader.
Exact filter parts are then compared at the historical and final heaps.

Stored literal congruence transfers those exact parts through actual
stored calls. All comparisons used to conclude Related share one final
reader. `LiteralPartsObservations.related` derives physical Empty
agreement separately from all finite observations. The proof does not
infer Empty agreement from Same alone or use unchecked cross-view
transport. Each observation compares both results in the same view.

The bare branch uses `PublicationBareParity.bare`. Both actual stored
calls then return the same available replacement by the literal reference
executor equation. It does not extend nonbare erasure to that exception.

`warm` is explicitly an actual-warm-call verifier. The public producer
`publication_binder_free` closes that call-completion boundary. It
constructs the body reconstruction at `common`, then the ordinary
reconstruction at the actual first returned heap. It returns their exact
equations, both final-reader warm replays, Keeps, output availability,
two local publication histories, and Related. No desired future output,
successful reconstruction, final heap, Cap, or range is an input to that
producer.

## Existing constructed checks

The nonbare fixture constructs a raw closed Mu replacement from Empty.
It builds a fresh smart publication with nested root unions, a bare local
union member, duplicate ordinary rows, different Bool guards, and ordered
repeated children. A captured alias equals the actual chosen ordinary
marker at level 1. That alias occurs only in a dead ordinary row. Another
capture is the complete raw Mu replacement. Initial Ready, callback
equations, reservation miss, Keeps, and replacement availability are
derived from these actual source calls. The fixture invokes the new
producer and retains both sequential schedules and final replays.

The bare fixture uses the real source union `[Empty, local, local]`.
Both filtered callbacks are proved to be their own bare reference.
It uses the same source-built recursive replacement and the same initial
producer. It covers normalization of duplicate bare self occurrences.

Both public witnesses are exact typed aliases to their checked private
witnesses. The selected public fixture source starts with the complete
strict fixture bytes. Neither witness takes a future callback success,
Ready state, output relation, or publication graph as a public premise.

The first failed fixture expected marker level 0. The captured Mu makes
the actual level 1. Its immutable failed snapshot and raw log remain in
the owning component. The successful second snapshot uses the actual
level and proves that fact.

## Validation inspected and remaining boundary

Selected evidence is `publication-filter-direct-8`,
`publication-filter-alignment-direct-3`, both canonical runs numbered 1,
`publication-filter-public-1`, `publication-filter-kernels-2`, and
`publication-filter-kernels-public-1`. The three selected strict logs are
genuinely zero bytes. Canonical logs report 608 and 614 jobs, respectively.
Public coverage is eight complete pairs plus two constructed pairs.
All eight printer options and explicit `#check @` are present. No printer
failure, omission, diagnostic, or nonstandard axiom occurs. Effective
MemoryMax and MemoryHigh are 4294967296 bytes; swap is zero.

BinderFree is a real static restriction on the publication body, including
ordinary child syntax. It does not restrict captured or replacement
records to depth zero. Arbitrary available recursive captures can remain
opaque or be reconstructed by the repaired executor. The proof does not
establish the general nested source-binder induction or chronological
earlier-winner alignment. It concludes Related, not physical equality of
the reconstructed results. It establishes neither outer node-key
exclusion nor general termination or Haskell correspondence.

This review checks existing evidence only: eight existing public pairs,
two existing constructed pairs, zero new pairs, and zero repeated builds.

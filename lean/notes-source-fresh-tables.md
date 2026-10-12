# Constructed fresh-name maps and environment lifts

`FreshEnvironment.lean` constructs the environment lift used by the local
entailment transport. The proof includes the source checked API's removal of
identity replacements. A name table with unique keys has the direct lookup
meaning even after that filter. Reversing a table with unique targets then
constructs an environment that recovers every mapped original value.

The reverse construction works on a finite relevant-name set. Its only
freshness condition is that new targets avoid the relevant names that the
table does not rename. `fresh_lifts` derives this condition from the actual
source fresh-name streams and their proved avoidance and length properties.
`fresh_entails_iff` therefore proves mathematical entailment invariance for
unrestricted environments when the query free names lie in the stated
ambient names plus the old fresh names. The environment lift is constructed;
it is not supplied as an unexplained premise.

`SourceFreshTables.lean` connects this name map to the executed source tables.
Equal guard reads give the same conflict entries and order. The two avoid
lists can differ, so the corresponding fresh streams are zipped. Both sides
have the exact conflict count, with unique keys and unique targets.

`allocated_rename` proves that every allocated source row is renamed by this
constructed map. Paths and declared sort names remain equal. `lookup_rename`
proves the first-match lookup behavior, including missing entries.
`declarations_rename` then proves the exact per-path table correspondence.
`tables_rename` includes the unchanged ambiguity list. These theorems apply
to conflicting signatures; they do not need the no-conflict restriction of
FullGuardPrune.

The remaining signature adapter must connect the source-resolved nested
scopes and their query formulas to this map. It must prove the free-name
bound used by `fresh_lifts`. Sorted environments additionally require the
declared-sort domain transport. The ambiguous sparse-to-complete case uses
a possibly non-injective quotient map, separate from the injective spelling
map proved here. SourceAliasTransport already states the corresponding
logical obligations without conflating them with exact solver verdicts.

Validation: `lake build MicroCFTA.SourceFreshTables` builds both modules with
the pinned toolchain. There are no proof placeholders or new axioms.

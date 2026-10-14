# One exact query specification for every Sized path

Updated: 2026-10-14 23:16 CEST.
Proof: `221bb23a`. Source base: `origin/main` at `f201deda`.
Repository: `TharkunAB/cfta`. Publish checkpoints on `formalize`.

## Source contract

`cfta-generator/src/Data/CFTA/Sized.hs` defines `sizedReference`, `sized`,
`sizedUpTo`, and the four queries of one class sequence. `fromClasses` reads
that sequence for listing, count, selection, and rank. The optimized branch
uses the count table only after its plain-constraint and ambiguity checks.
The solver-decided branch builds sizes 1 through the signed bound. Its table
lookup returns an empty class outside that range.

`SourceSizedApiLaws.Exact` is the shared query specification. It requires
finite class evaluations, exact distinct accepted terms per node-count size,
counts, invalid signed-position rejection, accepted-term rank coverage,
distinct size-major prefixes, and both signed rank/unrank inverse directions.
The public physical native entry already derives this specification. Read
[the entry note](notes-native-public-entry.md) for that result and its scope.

## Original-map reference and optimized dispatch

`SourceSizedFiniteKeysApiLaws` derives `public_exact`, `reference_exact`,
`native_reference_exact`, and `native_sized_exact`. These theorems use the
original guarded map language. Validation derives the finite carrier from
the actual keys. The original state type need not be finite.

The proof reuses complete query-record equality and exact original-language
membership. It retains canonical source order, ambiguous first-occurrence
deduplication, and the optimized count-table branch. Normalized original
equality annotations and lawful symbol comparison remain explicit.
No new product, scan, or row-language assumption is supplied.

## Bounded reference certificate

`SourceSizedBoundedReference.rows` retains every row and adds a complete-term
node-count guard. `classes_eq` proves literal ordered class equality through
the signed bound and empty classes afterward. The proof follows the actual
candidate recurrence and its strictly smaller child sizes.
It includes negative bounds and size zero. `accepts_iff` proves that the
certificate graph accepts exactly the original terms within the bound.
This is a proof certificate. The actual Haskell solver worker stays unchanged.

`SourceSizedBoundedApiLaws.fromClasses` models the four actual source queries.
`reference_eq` identifies that complete record with the bounded certificate.
`exact` derives all common laws from actual canonical order and membership.
The finite class certificates therefore cover every requested size, including
the empty classes above the bound. The class and rank order remain unchanged.

## Actual solver-decided execution

`SourceSizedFiniteKeysDecidedApiLaws.decided_exact` applies the common
specification to every successful actual bounded trace. Its language is
original guarded acceptance conjoined with the signed node-count bound.
`decided_complete_exact` derives a finite actual outcome from finite per-call
outcomes. The same trace retains its occurrence work and first error.
The evaluator can give different replies at different occurrences.

`SourceSizedFiniteKeysLiquidApiLaws.encoded_exact` applies the specification
to the actual encoded solver fold on original raw rows and raw trim keys.
Its language is independent mixed-sort ambient acceptance at the original
names and constraints, conjoined with the bound. `encoded_complete_exact`
derives a finite raw outcome from finite external attempts. Unknown and
raised failures retain their separate source channels. Response correctness
and external termination remain explicit per-call contracts.

## Validation and preservation

All five new modules are imported by `MicroCFTA.Audit`. The pinned Lean
4.34.1 aggregate build passes 1,554 jobs and checks dependencies of 44,359
theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-unified-sized-api-laws-20261014-audit.log`.
Focused logs are in the current preservation snapshot. Only the old unused
`inputs` warning remains. No production Haskell code changed. No previous
proof module changed except the audit import list. All fixtures and marked
drafts retain identical bytes.

Snapshot: `/tmp/mcfta-unified-sized-api-checkpoint-20261014-2316/`.
It saves all 1,933 Lean-tree files and four root documents. The previous
1,927 files remain. All backups, stashes, and other worktrees remain.

## Next connection

The explicit-map reference, optimized, and solver-decided paths now satisfy
the same complete query specification. Do not repeat these component proofs.
Next connect the general repaired cold path to the solver-decided result.
Derive successful validation from actual root membership and child closure.
Use `SourceFreshOrdinaryColdGuardedExact.trace_table_exact` for the original
independent guarded meaning. Reuse `SourceColdSharedRows.sizedTable` and
`sized_graph`, then the new encoded query theorem. The older prepared/first-order
liquid adapter does not establish that general repaired-source connection.

Keep concrete container operations, lazy heap scheduling, machine capacity,
external solver behavior, and verified Haskell extraction explicit. Preserve
the optimized interned core and older constructor/equality targets. Push
completed checkpoints regularly to `origin/formalize`. Do not deploy, send
messages, or post to the board. Check allowance and stop all work at 1% or less.

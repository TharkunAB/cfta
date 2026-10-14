# Repaired cold shared traversal and exact Sized classes

Updated: 2026-10-14 13:05 CEST. Proof checkpoints: `c410bc0a` and `75c50b4d`.

## Direct repaired executor

`SourceFreshOrdinaryColdSharedRows.collect` follows the native shared
worklist. It skips empty values and already stored identities. A first read
calls `MergedFreshOrdinaryExposure.nodeEdges`. The worklist stores the exact
returned ordered edges before it follows their children. Every next step
uses the actual cache returned by that read. Reader failures remain distinct.

`Trace` retains each actual read bound, ordered row list, intermediate cache,
and first insertion. `Trace.finite` derives finite worklist and uniform read
bounds for each finite trace. Every larger pair of bounds has the identical
result table and final cache. `collect_trace` recovers that exact trace from
any actual successful bounded run. No correspondence contract is supplied.

## General trace effects

`Trace.correct` follows actual repaired reads. Initial complete semantic
heaps, coverage, available closed work, and resident earlier rows suffice.
The exact final cache retains complete semantic heaps and coverage. Physical
growth and issued history preserve all earlier records. First insertions
extend the row map. Every final row retains an available closed root,
resident edge payloads, and closed children. Preparation and `NoNewMu` are
not premises. This theorem applies to a finite actual trace; it does not
derive general finite trace existence.

## Exact prepared bridge

`of_prepared` transfers the earlier finite prepared trace to the repaired
executor. `Trace.to_prepared` proves the reverse direction. Each induction
uses the derived prepared reader equality at the actual intermediate cache.
It also derives the preparation needed by the next step. Values, rows,
constraints, traversal order, identities, and final caches are identical.
The proof does not assume allocation-order equality outside this fragment.

`cold_finite` derives an actual repaired finite trace and stable executable
bounds for every prepared closed available root. It uses the existing
source-derived finite Mu inventory in precisely that prepared scope.
Existing exact table-language, native Sized, and solver-decided Sized
compositions therefore retain the identical physical table through the
derived trace bridge. Their validation and external solver contracts remain.

## Actual first-order Sized composition

`SourceFirstOrderFreshColdSized.source_sized` starts with arbitrary finite
binder-free body syntax and either source binder form. Actual repaired
empty-cache construction supplies the closed prepared result. Actual repaired
cold shared traversal completes without warmup or a supplied trace.
Its exact table supplies these laws:

- Each size class contains exactly the original guarded accepted terms of
  that node count. Each term occurs once.
- Each size class has a finite reference evaluation.
- Bounded prefixes are distinct, complete through the bound, and ordered by
  nondecreasing node count.
- Distinct-term rank and unrank satisfy both inverse laws.

The primary finite-key public native and solver-decided Sized contracts
remain unchanged. This result makes the repaired shared executor explicit
in the first-order construction path.

## Remaining obligation

Derive a finite repaired trace for arbitrary nested closed source outputs.
General single unfolding, bounded reader safety, and exact completed-read
replay are already proved. The initial Mu inventory and descending cached
depth are refuted as general measures by an actual closed source example.
See [native output and cold effects](notes-native-output-cold-effects.md).
General finite final tables and physical product language remain open.

## Raw-binder reconstruction boundary

`75c50b4d` adds `InternedStoredRawIdentityBoundary`. Actual repaired closed
construction builds `mu x. rawMu unused. f(x)`. Its open stored body contains
an unused raw Mu. Substitution replaces the outer reference with itself.
The exact resulting body has a different identity and cached depth 0 instead
of 1. Free-name lists remain equal. Kernel evaluation proves this observation.

The source's `substFree` comment states an unqualified physical identity
postcondition. That claim fails for this raw-binder case. `substitutionPlan`
rebuilds an open Mu body with smart `createMu`, which removes the unused
binder. It intentionally avoids pattern-synonym matcher fast paths.
A general reconstruction proof must model that cleanup. No language change
is claimed. Runtime behavior was not changed.

The live Haskell reproduction uses `createMu` outside and
`createMuDontCleanup` inside. It substitutes the outer `RecInt` with itself
in the stored body. The observation is `(False,1,0)` for equality and the two
nested-Mu counts. File: `/tmp/mcfta-identity-substitution-native.hs`. Log:
`/tmp/mcfta-identity-substitution-native-20261014.log`.

## Validation

Lean 4.34.1 passes 1,368 aggregate jobs and 42,779 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-raw-identity-20261014-audit.log`.
No Haskell source changed. The current upstream Nix suite and active-package
formatter checks remain valid.

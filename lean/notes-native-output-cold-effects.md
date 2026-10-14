# Native output scope and general repaired cold-reader effects

Updated: 2026-10-14 12:41 CEST. Proof checkpoint: `d87a4324`.

## Derived recursive scope

`SourceRecursiveIntersectionResultScope.Scope` permits only intersection
references from the incoming domain's seen pairs. Actual node and union
normalization retain child scope. A repeated pair is in the incoming domain.
A self return is closed because it passed the actual free-name guards.
The Mu body call uses the actual extended domain. Actual `maybeMu` removes
that selected pair from every returned free name.

`ScopeEffects`, `ScopeCalls`, and `ScopeRows` follow the exact source calls,
ordered walks, rows, references, and cache effects. `KernelScope.execute_scoped`
uses fuel induction over every source branch. Successful source returns
derive scope without an input preparation or output language premise.

`NativeResultScope.Meaning.request_scope` extracts actual completed source
execution from the exact guarded native meaning. The value and returned
machine are identical. `done_closed_of_ranges` uses the empty initial domain
to derive closed native output under the existing checked-word scope.
`cold_node_complete_closed` retains successful stable first execution.

## Original payload syntax

`OriginalOutput.original_of_free` follows coherent available record fields.
Every non-interned payload reference would propagate to the root free list.
A Mu removes only its own interned name. `closed_original` therefore derives
the existing `InputView.Original` predicate from closed available output.
`done_original_of_ranges` applies this result to actual native returns.
Probe metadata remains outside that predicate. The theorem does not claim
that all stored probe values have original payload syntax.

## General repaired reader effects

`MergedFreshOrdinaryColdEffects.collect_verified` follows the actual repaired
ordered worklist at every bound. Each actual single unfolding completes in
the retained semantic cache. Its result is available and closed. The proof
composes exact physical growth and issued history through later reads.
Ordinary rows remain resident and their children remain closed. Canonical
edge ordering retains those properties.

`nodeEdges_verified` covers direct node reads, the initial Mu fast path,
and the repaired closure fallback. Every outcome retains complete semantic
heaps and `Covered []`. It is done or exhausted. Pending constructors and
unresolved references are excluded. There is no preparation or `NoNewMu`
premise. Unfolding can allocate further Mu records.

`SourceRecursiveIntersectionNativeColdEffects.cold_node_read_effects`
derives successful stable native execution, closed original output, and
this reader invariant at every bound in the exact returned native cache.
It keeps the existing complete initial cache, closed Original input, and
checked-word scope. It assumes no output preparation or cold-read success.

## Remaining obligations

Exhaustion is still possible in the proved bounded result. Finite repeated
traversal needs a source-derived finite physical inventory or another
well-founded measure. `LexicalBinderClosure` derives a finite abstract
syntax inventory. Physical allocation and canonical replay have not yet
been connected to it. The old initial-cache inventory requires `NoNewMu`
and does not prove this general case.

Finite final cold tables, physical `ProductReadback.members` and `.rejected`,
and exact product language remain open. Do not infer those results from
closed output, original syntax, or bounded reader safety.

## Validation

Lean 4.34.1 passes 1,363 aggregate jobs and 42,587 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-general-cold-effects-20261014-audit.log`.
No Haskell source changed. The current PR #119 Nix and active-package
formatter checks remain valid.

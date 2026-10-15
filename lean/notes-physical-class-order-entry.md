# Physical class order and source equality selection entry

Updated: 2026-10-15 02:13 CEST.
Proofs: `ae6a0141`, `ac7c1eaf`, `97f987a1`, and `a84343e3`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
Publish completed checkpoints on `formalize`.

## Exact installed sorting schedule

The project plan selects GHC 9.14.1, base 4.22.0.0, ghc-internal 9.1401.0,
and containers 0.8. The installed source is at
`/home/tritlo/.ghcup/ghc/9.14.1/share/doc/ghc-9.14.1/html/libraries/ghc-internal-9.1401.0-e31e/src/GHC.Internal.Data.OldList.html`.
The extracted source is `/tmp/mcfta-ghc9141-OldList.hs`. Its SHA-256 is
`4b519356f7bcbd705866551e26552c84b08d527fe93b060cc89b27882aec6248`.
It records `sortBy cmp = actualSort (\\x y -> cmp x y == GT)`.

`SourceListSortMerge` retains the actual binary, fused three-way, and fused
four-way workers. It includes their held-head helpers and empty-run branches.
`SourceListSortRuns` retains descending reversal and the original ascending
function accumulator. `SourceListSort` retains short inputs, natural runs,
the special five-run and six-run reductions, and the exact full merge loop.
The totalized empty merge-loop case is unreachable from natural-run output.
All workers terminate on finite lists. Exact count and permutation theorems
retain duplicates without a lawful-comparator premise.

This is a manual source model checked against the installed definitions.
It is not a verified GHC or Haskell extraction theorem. No different sort
algorithm is substituted. The strict evaluation annotations do not establish
native lazy scheduling or resource bounds.

## Physical trie and path-set comparison

`SourceEqualityClassOrder.Record` retains the source trie and ascending set
enumeration. `Coherent` states trie validity, canonical path enumeration,
and exact shared membership. `trie_subsumes` derives the actual strict-prefix
meaning from the existing structural trie theorem.

`completedCompare` follows `completedSubsumptionOrdering`: first-to-second
strict subsumption returns less; second-to-first returns greater; the fallback
compares the second set to the first. `completedCompare_exact` gives the
independent path-list readback. `ordered` runs the installed source sort on
these physical records. `orderedPaths` supplies their exact ascending path
lists to the gate. Occurrences and coherence are retained.

`recordOf` and `recordsOf` construct both physical fields from supported
path sets. `normalized_records` derives coherent complete records and exact
canonical payload readback from the terminating normalizer. Existing
normalized subsumption transitivity and irreflexivity remain available.
They are not assumptions about arbitrary raw class lists.

`SourceEqualityClassOrderExamples` contains three coherent raw records:
`[[0],[1,0]]`, `[[1],[2,0]]`, and `[[0,0],[2]]`. Their comparator has a strict
cycle. The source's three-item merge returns the third, second, and first
records. A right-associated merge returns the first, third, and second.
The kernel checks these results. Haskell confirms the cycle, exact source
order, and rejection when the three classes are normalized together.
Probe: `/tmp/mcfta-source-class-order-probe-20261015.hs`.
Log: `/tmp/mcfta-source-class-order-probe-20261015.log`.

## Source guards and complete selection entry

`SourceEqualityPrecheck.Constraint` distinguishes `EqContradiction` from a
physical class payload. The unused native constraint identity is erased.
`combine` retains contradiction absorption and the both-empty fast path.
Its nontrivial case uses the already proved terminating normalization bound.
`combine_complete` and `combine_exact` require no completed call premise.

`precheck` runs the empty and combined-contradiction guards before the unsafe
ordered accessor. `precheck_safe` proves that the source live branch cannot
pass contradiction to that accessor. `live_payload` retains the exact
original payload and installed source sort result. Early branches contain
no gate calls.

`combineArray` uses the existing actual parent-array normalization schedule.
`combineArray_eventual` derives sufficient work and exact combined-result
readback. `precheckArray_eventual` retains the full branch, physical order,
and unsafe-accessor behavior. The bound is derived, not supplied.

`SourceEqualitySelectionEntry.runChecked` runs only the work required by the
preceding guard result. `run` and `runArray` install complete and actual-array
guards. `Execution` retains both actual memo graphs in the live selection
branch. `complete` derives finite gate fuel, exact result and returned cache,
and both memo invariants. Early branches retain every table. `source_edges`
derives the initial constructor cache from the original source expression.
`source_array_edges` also derives finite actual parent-array normalization.
It retains one sufficient work bound and stable gate execution at all larger
bounds. No successful construction, normalization, or gate premise is given.

The caller takes physical constraint payloads as input. This proof does not
derive native constraint-cache storage or connect every original encoded
annotation to a physical allocation. The entry ends at selected classes,
before native required-path and narrowing operations. The concrete scalar
guard wrapper remains noncomputable in the existing logical source model.
The exact Sized contracts and optimized interned core remain.

## Verified raw self-binder boundary for the next primitive

`createMuDontCleanup id` is an exported raw constructor. It retains a closed,
unconstrained Mu whose body is its own reference. `unfoldOuterRec` returns
the same node. The completed gate returns false for every path at this node.
The source `requireNode needed n@(Mu _)` then unfolds at the same demand.
The strict open-Mu rank does not apply to this closed node.

`SourceClosedSelfRequireBoundary.actual_stutter` checks actual repaired
construction, closedness, the visited predicate, exact stored unfolding
stutter, and a clear gate at every path. This fixture uses the existing
Nat/Unit constructor model. It contains no project axiom or native evaluator.

The preserved Haskell reproduction uses two such children and the class
`[[0,0],[1,0]]`. It prints `(True,True,True)` for closedness, the source
predicate, and unfolding identity. Forcing the first reduced child times out
after two seconds. This timeout is runtime evidence, not a formal theorem
about all native executions. The exact kernel stutter and source Mu branch
identify the progress obligation independently of the timeout.

Run the reproduction inside the project environment:

```sh
nix-shell --run 'cabal exec -- runghc -package=cfta lean/repro/RawClosedSelfRequire.hs'
```

Log: `/tmp/mcfta-raw-self-require-probe-20261015.log`.
The new reproduction is formatted with fourmolu. The three older Haskell
repros and all marked drafts remain unchanged. No production Haskell code
changed. The unchanged library suite was not rerun for these proof additions.

## Next proof and repair

Model the actual `Needed` trie, `insertNeeded`, `requireList`, and
`requireNode` in `Data.CFTA.Equality.Operations`. Reuse finite selection and
actual cache readback. Address closed raw self stutter with a repair that
preserves the least language of the full exported input domain. Do not
silently exclude raw constructors. Keep the optimized interned core and
ordinary fast paths. Inspect `editAll` and other same-path Mu readers for
the same failure. Do not infer required-path termination or repeated
fixed-point termination from the completed gate.

The existing leaf and nested-unary required-path/edit proofs remain. Read
`notes-equality-leaf-require-exact.md`, `notes-equality-nested-unary-root.md`,
and the actual worker before extending them. The unary ancestor root theorem
is complete; do not resume its archived draft. Native primitives, lazy
scheduling, resources, external solvers, and extraction retain their limits.

## Validation and preservation

All eight focused Lean modules pass with pinned Lean 4.34.1. The aggregate
audit passes 1,617 jobs and checks 45,336 theorem dependencies. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. Only the old unused
`inputs` warning remains. Audit log:
`/tmp/mcfta-physical-class-order-entry-20261015-audit.log`.

Snapshot: `/tmp/mcfta-physical-class-order-entry-checkpoint-20261015-0213/`.
It saves 2,007 Lean-tree files and four root documents. All older proof bytes
except audit imports, fixtures, counterexamples, drafts, backups, stashes,
and other worktrees remain unchanged.

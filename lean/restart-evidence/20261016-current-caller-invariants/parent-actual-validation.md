# Actual current local and parent receipt validation

## Result

Seven new source files are frozen. Their complete SHA256 values are in `parent-actual-SHA256SUMS`. The copied source snapshots end in `.frozen.lean.txt`. No old proof, Haskell, Audit, or project documentation file was edited by this worker.

Focused command:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedParentEdgeActual MicroCFTA.SourceCurrentPrimaryReadsCounterexample
```

Terminal result: 0, 1,407 jobs, `parent-actual-build-1.log`. The only warning is the existing dependency unused-input warning. The counterexample is owned and reviewed by another worker.

The earlier focused foundation and source-erasure checks passed 1,267 and 1,250 jobs. Raw logs are retained.

Public direct command:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-caller-invariants/parent-actual-public.lean
```

Terminal result: 0. There are 31 public axiom checks, 31 full signatures, and 12 external kernel examples. Four named external kernels also have axiom checks. The probe reports no errors, warnings, or sorryAx. Only propext, Classical.choice, and Quot.sound occur. The final raw log is `parent-actual-public-4.log`. Structured results are in `parent-actual-checks.json`.

The actual kernels cover raw parent rejection with no child/load/range obligations; unchanged and empty local returns with the Scan range plan derived impossible from the literal prefix equation; and actual empty Scan, required worker, class pass, and propagation. Foundation kernels cover current fourth-memo hits, open misses, empty and exhausted worklist skips, and read-list identities.

## Public contracts

- `SourceCurrentAllocatedConjunctionReadValidity.call` derives final validity and retention for the SUPPLIED current conjunction reads. The supporting ten theorems follow its actual exposure, class, tuple, requirement, and worklist prefixes.
- `SourceCurrentConjunctionRequiredActual.required_unique` identifies only completed required results and constructor heaps. `verified` derives the physical and language receipt at the supplied required return.
- `SourceCurrentAllocatedPrimaryErase` exports five erasures from exact source primary reads to the old receipt family.
- `SourceCurrentAllocatedScanSourceReads.ScanReads` replaces each primary receipt by the exact source family. It retains current query reads and source short-circuit order. Its erase theorem retains the literal old trace and memo endpoints.
- `SourceCurrentConjunctionScanClassPassActual.Reads` uses strict Scan reads and the supplied required and class-pass reads. `verified` derives the full receipt for that same return. `from_scan` and `finite` CONSTRUCT strict schedules from initial invariants and finite reached plans.
- `SourceCurrentAllocatedLocalReductionActual` derives the actual precheck receipt and full local return. `Ranges` contains only the reached Scan range checks. `ranges_of_finite` projects an existing stronger finite plan. `finite` constructs strict local reads.
- `SourceCurrentAllocatedParentEdgeActual.verified` derives the full parent receipt at its SUPPLIED result, checked state, fourth memo, merge memo, and final global bundle. Its live input plan is conditional on raw contradiction being false. The rejected branch needs no local field load, inherited readiness, child availability, or local ranges. `finite` constructs a strict actual parent schedule from the existing finite plans.

## Premises and limits

The legitimate warm entry keeps initial Ready, inventory At, fourth-memo Correct, merge Stored and CacheCovers, and three-table Valid explicit. Live branches retain normalized Cached/load, inherited Ready, original child Values, and actual Scan word-range checks. Finite construction also needs class-pass reached range plans. Actual verification does not need those future completion plans.

The strict source read condition repairs an older model indexing gap at the primary closed endpoint. Old unanchored Reads alone do NOT imply strict Reads or arbitrary final memo validity. Erasure is one-way. All old source definitions remain unchanged.

The parent language is narrowing for every result term. Under inherited satisfaction it is equivalent to the original raw guard and original child forest. Unrelated child values can remain open. The proofs do not assert every child is closed or that the result children always have the original arity: constructor rejection retains the literal sentinel.

No theorem transfers these serial graphs to GHC lazy evaluation, unsafe global memo publication, native HashMap/IntMap implementation, or wrapping machine identities. No whole mutually recursive reducePartially completion theorem is claimed. Actual source-facing outer traces need the new strict read refinement and their physical, range, and language invariants.

## Independent integration review

`actual-receipts-independent-review.md` reviews PartialFrames, PartialSourceReads, and ProbeActual. `parent-probe-same-return.lean` checks a joint physical/language receipt and filtered ProbeHeap at the same supplied parent return. It does not substitute another finite execution.

# Current conjunction worker validation

Checked 2026-10-16 12:56 CEST. The three owned source files are frozen. No owned process remains. The canonical Lake slot was released to the parent.

The final focused command was:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentConjunctionWorkerCompletion MicroCFTA.SourceCurrentConjunctionWorkerStability MicroCFTA.SourceCurrentAllocatedConjunctionWorker
```

`worklist-build-2.log` records terminal exit 0 and 1199 jobs. It includes the root-owned checked-state lift. Only the existing dependency unused-input warning appears. The first batch log is retained. Its core worker target passed, but the first root checked-lift proof failed. The parent corrected that proof before the final batch.

The final direct source logs are `worklist-direct-2.log`, `worklist-completion-direct-3.log`, and `worklist-stability-direct-2.log`. All returned exit 0 without new warnings.

The two imported probe commands were:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-conjunction-worker/worklist-public.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-conjunction-worker/worklist-public-kernels.lean
```

Both returned exit 0. `worklist-public-1.log` contains 15 public axiom checks and 15 complete signatures. The only foundations are `propext`, `Classical.choice`, and `Quot.sound`. It contains no `sorryAx`. `worklist-public-kernels-1.log` is empty. Its seven kernel examples check these cases:

- Exhausted admission budget drains every pending item without a row read or state change.
- A literal memo hit precedes the open guard. An explicitly unverified cache can return its stored true answer for an open reference. This test makes no semantic claim for that cache.
- A cold open miss returns false at zero projection/read bounds and stores the original query.
- Closed Empty returns true at budget zero without row reads.
- A failed admitted row retains the reached table, pending queue, and exact returned physical state.
- Initial physical readiness, query residency, and memo correctness produce a finite successful call with sound retained answers.
- Two successes at different lower bounds have the same answer, constructor heap, equality operation state, and fourth memo.

`worklist-checks.json` records counts and source hashes. The `.lean.txt` copies preserve the checked owned sources. No compiled artifacts are stored in this evidence directory.

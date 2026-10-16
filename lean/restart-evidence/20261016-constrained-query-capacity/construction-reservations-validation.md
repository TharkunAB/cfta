# Static construction reservation validation

Validated at 2026-10-16 18:29 CEST. Source SHA256 `2117425941937f595604135366d1da424830e7cf00880ae3b80c148974428225`; 160 lines.

The pinned direct source check passed with exit 0 and no warnings in construction-reservations-direct-2.log. The initial failed direct log remains. Root-owned canonical construction-reservations-build-1.log passed with exit 0 and 177 jobs. No warning occurred in that focused log.

The imported public check passed with exit 0 in construction-reservations-public-1.log. All 11 declarations have full explicit signature and axiom checks. The imported integration check passed with exit 0 in construction-reservations-kernels-3.log. Five checked integration theorems cover duplicate source rows, missing variables, serial warm construction, static source-key admission, and supplied actual capacity. Both earlier failed kernel logs remain. The final logs contain no errors, warnings, or sorryAx. Only propext, Classical.choice, and Quot.sound occur.

Direct commands used `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean` and `LEAN_PATH=lean/.lake/build/lib/lean`. The source check emitted only `/tmp/SourceCurrentAllocatedFiniteOrdinaryConstructionReservations.olean`; it was removed after canonical validation. Imported probes emitted no compiled artifact. No Lake, Haskell, Git, board, or network action ran from this task.

# Shared forecast validation

Final source: `SourceCurrentConstrainedCapSharedForecast.lean`.
SHA256: `3ed5092e36a581fa294a8c046995444589b5ea3dc53151af35a9228a9105ecb0`.

- Strict absolute-path Lean 4.34.1 check: `shared-forecast-direct-2.log`, exit 0, zero bytes.
- Root canonical target: `shared-forecast-canonical-1.log`, exit 0, 1515 jobs.
- Imported public checks: `shared-forecast-public-1.log`, exit 0, 25 full signature/axiom pairs.
- Imported pure kernels: `shared-forecast-kernels-1.log`, exit 0, 3 full signature/axiom pairs.
- Final imported logs contain no warning, error, truncation, or `sorryAx`.
- The probes enable explicit names, universes, proofs, deep terms, and 10000000 print steps.
- The only reported axioms are `propext` and `Quot.sound`.

Attempt 1 used an invalid namespace notation. Its exact source and failed log remain.
Attempt 2 replaces that notation with an explicit `open` list. It changes no formula.
The canonical log replays an inherited dependency warning. The new source check is empty.
The public and pure kernel checks write no `.olean` file.
The verifier checks the frozen files and the complete imported pairs without rebuilding.

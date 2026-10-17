# Edit receipt validation

Final source SHA256: `3f8ade76cd44bc1c38d85e9a1de469d230c1956ed0633090526345d48395f789`.

- Strict absolute-path Lean 4.34.1: `edit-receipt-direct-1.log`, exit 0, zero bytes.
- Canonical single target: `edit-receipt-canonical-1.log`, exit 0, 1527 jobs.
- Imported API: `edit-receipt-public-1.log`, exit 0, 10 complete signature/axiom pairs.
- Imported integrations: `edit-receipt-kernels-4.log`, exit 0, 2 complete signature/axiom pairs.
- Final imported logs contain no error, warning, truncation, or `sorryAx`.
- All probes use explicit full names, proofs, universes, deep terms, and 10000000 print steps.
- Only standard axioms `propext`, `Classical.choice`, and `Quot.sound` are allowed.

Production passed its first strict attempt. Three failed integration attempts
remain with exact snapshots and raw logs. Corrections make the literal absent
lookup and rebuilt constructor equalities explicit, open the Cache namespace,
and reduce the empty-map population and allowance predicates.
The final integration proofs use no full-worker evaluation.
The canonical log replays an inherited dependency warning. The final strict
production log is empty. The verifier checks frozen files without rebuilding.

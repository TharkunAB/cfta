# Protected prefix linter correction

Status: frozen. The current production source is `SourceEqualityNativeDemandProtectedPrefix.lean`, SHA-256 `393144b7de1b30e1cd078559ce12d09d03ca625069593677b106cdb26890ecb0`.

The earlier direct checks enabled the two unused-variable linters. A later check with all linters enabled reported three `linter.omit` warnings. The correction removes the global instance declaration and its three `omit` wrappers. The same two instance parameters now occur explicitly on the seven theorems that use them. No theorem proof body or result behavior changed.

The original production bytes remain at `protected-prefix-before-linter.source.lean`, SHA-256 `10c94c24f825b70b2443e32a18ceb10f6faec69133a912153458d6ba820833b0`. The original `protected-prefix-manifest.json`, sums, source snapshots, review, public file, kernel file, and logs remain unchanged. The original manifest is a historical record of that source version. Resolve its production entry through the exact preserved source snapshot.

The new strict direct check uses `-Dlinter.all=true`. `protected-prefix-linter-final-direct-1.log` is empty and exits 0. The final root strict log is also empty. The final canonical build and full Audit pass in `lean-audit-final.log`, with 2711 jobs and 61656 checked theorem dependencies. The earlier audit remains at `lean-audit-before-protected-linter.log`.

The original public and integration source files were rerun against the final canonical module with all linters enabled. All ten public axiom/full-signature pairs pass in `protected-prefix-linter-final-public-1.log`. Both constructed publication pairs pass in `protected-prefix-linter-final-kernels-1.log`. Both logs contain no warning, error, or `sorryAx`.

The old and new full public logs are byte-for-byte equal. Therefore the complete printed public signatures and axiom reports did not change. The supporting `protected-prefix-linter-final-signatures.json` records this equality and both hashes.

The scope remains actual body/frame prefix decomposition and exact captured-owner publication. No initial-only query-capacity or whole reduction claim was added. This correction changed only the owned production module and new evidence files. It did not change older frozen evidence, another production module, Haskell, Git, or Audit source.

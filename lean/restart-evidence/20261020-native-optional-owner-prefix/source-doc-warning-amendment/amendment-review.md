# Canonical-warning metadata amendment

Reviewed on 2026-10-20 19:33 CEST. The correction is valid. It changes one source pin in the installed source/document manifest. The preserved pre-correction manifest has SHA256 `1fbc876245a89dbf12315652123e44a84948f89301218ad8df036b4e5e2965a3`. Its bytes equal the frozen original review manifest. The refreshed manifest has SHA256 `1c0fc50717df686b3b7b9aeafda30158f1a0b2090d4dd5ed46d3548e2d798b90`.

The only changed pin is `selected-canonical-warnings.json`. All other source pins, artifact pins, checks, script bytes, review, ranges, documents, proof sources and raw receipts remain unchanged. The new mapping records the exact earlier ClosedCompletion unused-input warning for all nine module mappings. All eight distinct selected canonical logs contain that same warning and no other warning. Query and Mu share one canonical job. The correction adds no warning and changes no proof claim.

The current installed source-doc-verify.py was run from cwd=/ with --root and --live against the refreshed manifest. It returns PASS with empty stderr. It still verifies thirteen ranges, twelve public and one constructed readback, ten empty strict logs, eight canonical jobs, sixty-two commands and seventeen failed commands, Audit 3504/74153 and the unchanged Haskell/package inventory.

The original /tmp source/document package remains frozen and unchanged. This amendment package adds no Lean job, proof pair, source edit or document edit. Its standalone verifier checks the exact one-pin difference, the actual warning mapping, all eight raw logs and the successful refreshed live readback.

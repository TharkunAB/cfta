# Main refresh final source and documentation review

Status: **CLEAR for evidence archive and final preservation**. Reviewed 2026-10-24 00:51:05 CEST. No documentation or source blocker found. Root authored the merge, repair, probes and new documentation. I authored the earlier program-source assessment and reviewed the repair. I ran only read-only Git, text and static identity checks for this review. I did not run a compiler, test, prepared program or network operation, or change repository files.

I read the complete 108-line focused note, complete 36-line new update, and complete first external Haskell repair index in FINDINGS. The new material states the actual partial-result contract, the changed empty-node callback order, incremental typing, encoding-dependent type merging, finite-test limitations, runtime parametricity assumptions, parallel and resource obligations, and the no-stop bridge target. It preserves H6 as the strongest combined result and the full goal as active. It does not claim a new Lean theorem or Audit, a compiled/proved H39 counter-consumer, an LPO repair, or a completed refresh push.

All nine actual document hashes match document-changes.json. Removing the one exact 36-line update restores each of the eight ordinary documents byte for byte. In FINDINGS, removing that update and reversing only the deliberate first repair-index replacement restores the complete old document byte for byte. All prior findings below the first historical checkpoint remain identical. The first index retains both earlier repairs, adds the local negative-depth fix, and lists both LPO defects as open. It does not present an annotation-only LPO change as sufficient.

The actual HEAD is 058b11fe8f3706460156d7a1fc454063406a4634, parent merge 78904be72914616af4bf41046ab27f65a60c6142. All 34 listed upstream paths at the merge match 6b62b4afefca80bb05f5a37546212a99980aa3df, including modes. The two repaired files match type-depth-fix-report.json. Rewriting.hs still matches imported main, so the two native LPO regressions are accurately described as unfixed. Git shows no change to the earlier Lean modules or local Equality/Operations.hs between the previous pushed checkpoint and the repair HEAD. The merge report records 125997 baseline files and 125970 unaffected paths; Root's pending final preservation remains the authority for the complete filesystem set.

The retained evidence supports the stated validation scope:

- haskell-tests-host-path.log records 325 examples with zero failures and PASS for both unit-tests and the complete golden suite. The golden source runs checked and unchecked variants but selects phase 1. The earlier Nix libgmp link failure remains separate.
- typing-probe.log contains the strict-warning builds of both libraries before its later temporary harness compile failure. The focused note correctly retains that distinction and the host linker metadata warnings. It does not call the whole failed harness attempt a PASS.
- native-probes.log contains nine successful core checks before its later package-exposure harness failure. These include the deliberately speculative EmptyNode hole and separate exclusion catalogs. The note accurately limits this evidence.
- pending-probes-v2.log confirms both well-typed LPO defects: [LT,LT,LT], also after canonicalTypes, and GT reversing to LT inside function application. The retained wrapper compiles with -Wall -Werror and runs the typing probe at -N2. Its successful checks cover all three negative-depth entries, depth zero, and equal returned laws in the three small phase-4 modes. The temporary signature uses reverse and the empty list, size 3, depth 1 and four extra rechecks. The log reaches phase 4 but finds no additional phase-4 law; the note claims only a signature-specific smoke result.
- format.log checks the stated 23 Haskell files and both Cabal files. The note does not claim committed new tests.

The focused note names the intended final evidence directory. That directory was not present at this review cut, as expected before Root archives these records. Archive the retained reports, sources, failure logs and corrected attempts there, then run the planned final preservation check before publishing. This review does not claim either future operation or a future push has completed.

## Review-cut hashes

- `/home/tritlo/Code/mcfta/lean/notes-current-upstream-program-enumeration.md`: SHA256 `1d54884943cd1afaa14a1d08d2259cbe322022941d50f6e46293e702f45a176a`.
- `/tmp/mcfta-main-refresh-20261024/document-changes.json`: SHA256 `514f70fea65f6dce7244f8a11d8bb8e1a19e75ffa163dde62552b1227420a613`.
- `/tmp/mcfta-main-refresh-20261024/merge-report.json`: SHA256 `08105b8fc35aff4ac7fd3c68db7c10f2d54763db9f87dc7f5e889bf875b99491`.
- `/tmp/mcfta-main-refresh-20261024/type-depth-fix-report.json`: SHA256 `e40450eca67a30a68dcc0fddee2c6be805f251b1b05d32767bbad786cf2f4068`.
- `/tmp/mcfta-main-refresh-20261024/pending-probes-v2.log`: SHA256 `3ac328edeb02fb7eac86083392d18680a3ba7153e5d860051a4c32a6b1a52590`.
- `/tmp/mcfta-main-refresh-20261024/native-probes.log`: SHA256 `69c35e8721e8b84f2f9287d686575b024448cce466c6aced761962c999ed6b9f`.
- `/tmp/mcfta-main-refresh-20261024/typing-probe.log`: SHA256 `5775fcd2f070d88a6b55d7730457f0e9ccfe703fde16f1787af08e94f3a42e13`.
- `/tmp/mcfta-main-refresh-20261024/haskell-tests-host-path.log`: SHA256 `763f111d8805c01d882fc13214ee0a8bfd8e13c125c655d3891fd70158cc2c4d`.
- `/tmp/mcfta-main-refresh-20261024/haskell-tests.log`: SHA256 `235ca74ae3bf9e5f0f6e282fcac1a1cce0565a2dc1324f78917a17bc9830140f`.
- `/tmp/mcfta-main-refresh-20261024/format.log`: SHA256 `5d2817d90102050e3c894f232a9cbf8922b4ba563473444ed517785f16a865a2`.
- `/tmp/mcfta-main-refresh-20261024-programs-review.md`: SHA256 `d7a2a43666b6c1f0fed26f5a92ee9d7c252f019508a97bc239aca59618e77816`.
- `/tmp/mcfta-main-refresh-20261024-pruning-review.md`: SHA256 `aedf70730f77e77c0a0d0bfd872962f652bc3456ec29482bca6d7ce2c5f1de14`.

The nine document hashes are retained in the reviewed document-changes.json above. No existing artifact was edited by this review.

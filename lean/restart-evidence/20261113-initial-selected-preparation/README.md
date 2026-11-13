# Initial selected preparation: restart packet

This packet preserves exact source stages and captured compiler evidence.
The proposed installation path is `lean/restart-evidence/20261113-initial-selected-preparation/`.
It contains no build archive or broad source snapshot. The large source-pin table contains hashes.
The Audit base is the actual import-table input.
No compiler, live edit, Git operation, Haskell change, or board action was used to assemble this packet.
The earlier initial-root and initial-prefix restart packets remain unchanged.

Run `python3 check.py` for source replay. It requires Python 3 and GNU patch.
It reconstructs all stages in a temporary directory, uses `--fuzz=0`, rejects offsets,
and verifies stage hashes, exact compiler-input hashes, captured exits and printed axioms.
It does not run Lean or Nix. A fresh compiler check requires the original pinned source tree and environment.
`checkers/` preserves the exact historical runners, including their original qualified declaration names and paths.

## Exact source stages

| Raw stage | Lines | SHA256 | Recorded status |
| --- | ---: | --- | --- |
| `prefix-raw-235` | 235 | `8eba0fbcb07666c58a73cb0df08ef2bdaab1e6af959428fc234ba20dc790861c` | strict-pass-prior-checkpoint |
| `prefix-public-236` | 236 | `786a7f5f1f3938fd720eecfcbef94608f625377c36af66138532bfc800f265e6` | strict-pass-public |
| `facts-public-101` | 101 | `a6e7b4874537313f62fdf4416bf64dbb1ecafb2a1c17eae57f99992114a43ab4` | strict-and-import-pass-first-try |
| `preparation-failed-395` | 395 | `6d9243ec6e95984c7518df7bddadba5714f7512b45db37d6811b873dd4070d66` | strict-failed-check1 |
| `preparation-root-failed-396` | 396 | `733f45748246dcf5720d82596f38bb988922cb4ce62f427c9cc4d88f9e38916a` | strict-failed-check2 |
| `preparation-failed-394` | 394 | `f16e381df0cafc01ea3be852c6159848d9ae37f11550ea5ade560b91addb1e99` | strict-failed-check3 |
| `preparation-checked-398` | 398 | `7e864f2064932f0b4e729c731598f300e5026dfbd392bf979d168eed278eab9d` | strict-pass-check4 |
| `preparation-public-399` | 399 | `2bb62855b0b83a79aaf2d2aae30d6d502fc9cf3c2a77bceee8c01ae904562a38` | strict-pass-public |
| `scan-append-public-49` | 49 | `997933df32672c54609d4359a06532007c87f3e03ef6768f05334f1fd44e8101` | strict-pass-first-try |
| `zero-raw-29` | 29 | `423024a3ae4c2fc1ef2865f9d1aaee6d4611199cd00f0cc842d2c440bed6e185` | strict-pass-first-try |
| `zero-public-29` | 29 | `5bfdf8117fced2034a7d28b27543ce7ad36f5249ffa3e133e38fdd8b704c9c63` | full-build-and-public-import-pass-comment-only-change |

Eight bases and 17 ordered GNU unified diffs reconstruct 25 stages:
11 raw sources, 13 actual strict/import inputs, and the prior Audit import table.
`manifest.json` records each original path, parent, hash, byte count and line count.
The original Root and source-owner repair patches remain separate from the generated replay diffs.
The exact 52-line preparation header remains unchanged across all four private source stages.
The public 399-line stage adds its public declaration and documentation without changing that statement.

All original preambles, headers, helper fragments, body fragments, source pins, provenance and notes are preserved.
The private prefix235 is the prior checkpoint's checked final source. Its raw and strict input are both retained.
The public prefix236 promotion is a separate source stage and a separate actual strict input.
Facts101 and scan_append49 retain their first successful raw strict inputs.
The facts module's actual import check is another distinct input.
Zero29 retains its original public theorem source and first strict check. The final public source changes only its comment.
That comment reads: “Source construction succeeds at size zero. No Program has zero components.”
Historical notes that say “uncompiled” remain unchanged. Later compiler reports record the actual outcomes.

## Captured checks and publication

Ten earlier focused calls are retained separately: seven passes and three preparation failures.
They include one checked private prefix input from the prior checkpoint.
All diagnostics are preserved in full, including `error(lean.invalidDottedIdent)` in preparation checks 2 and 3.
The final private398 input passed check4. No failed source or diagnostic was replaced.
The generic checker script is byte-identical at all ten locations and is stored once with all original paths.
Its legacy `public_laws_added=0` field is preserved as recorded; it is not a count of the later public API.

The final publication report was present and PASS before assembly accepted it.
Its four recorded compiler calls are full Audit build, public preparation strict check,
explicit-qualified public imports, and full strict Audit.
Each returned 0 and printed only standard axioms. The import check observes all five public declarations.
The final checker reused unchanged prefix236, facts101, and scan_append49 strict sources;
it did not repeat their earlier compiler calls. Raw strict, import, and final inputs remain distinct.
This packet replay does not rerun any compiler.

`publication/final-checked.json` records 5911 modules, 4909 Audit imports, and 95033 theorem checks.
The same captured source-pin table has SHA256
`102d5b24ba5d8e9320b0e6fb094a1327fb9f55d771111a2a512a5b669c5a6cbc`.
Replay binds every public source and the actual final Audit input to that table.
The code commit `e38047c8612210b43bfe0406c2a276d6714310a1` was reported by Root.
This packet records no independent Git or remote verification.

## Checked scope

The checked prefix and preparation observers follow the same actual initialized root,
active prefix candidate, narrowed native result and heap, encoded handle, Entry and SelectedPreparation.
They derive ordinary identity and full original source-row inclusion from the observed execution.
They add no Packet, Ready, model, desired source row, native Parent call, or future output supplier.
The standalone append law preserves the actual ordered scan and its complete continuation result.
These are conditional actual-execution observations. They do not assert that a successful branch or an output exists.
The zero theorem establishes front-end success at size zero and excludes a Program at that count.
It makes no native-language emptiness claim and does not refute per-emitted-output finite completion.

## Unproved material

`UNPROVED-joint-witness-audit/` preserves the exact audit94/bff5d66c and same-output target10.
The target asks for one completion of the same actual partial root accepted by the same ORIGINAL source value.
It is not a supplied model or a checked semantic theorem. Finite Type witnesses and joint satisfiability remain open.
The zero draft's explanatory note remains under metadata and retains its narrower count-only scope.

`UNPROVED-actual-shared-visitor/` preserves the exact header105/5a7c65ac and plan66/5d8687d9,
plus its preamble, pins and original frozen metadata. This next actual shared-visitor attachment has no body or compiler check.
Do not count it as a proved row-scan attachment or a future provider.
The primary eager path remains shared. The historical nonshared Parent observer is a separate operational entry.
Default/Haskell correspondence, finite-model creation, semantic pullback, output existence and completeness remain separate.

`replay-checked.json` records the source-only replay. `SHA256SUMS` covers every packet file except itself.

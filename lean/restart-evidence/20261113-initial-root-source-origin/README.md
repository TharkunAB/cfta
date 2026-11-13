# Initial root source origin: restart packet

This packet stores exact source stages, source patches, checker inputs, checker scripts, and reports.
It contains no Lean build archive. No Lean, Nix, or Git command was run to assemble or replay this packet.
The proposed installation path is `lean/restart-evidence/20261113-initial-root-source-origin/`.

Run `python3 check.py` for source replay. This command requires Python 3 and GNU patch.
It reads only this packet. It reconstructs every recorded stage in a temporary directory.
It applies each GNU unified diff with `--fuzz=0`. It rejects every reported offset or fuzz adjustment.
It verifies source hashes, exact strict-input hashes, captured check exits, standard axiom reports, and source pins.
It does not rerun a proof check. A fresh Lean check requires the pinned repository, toolchain, Nix environment, and recorded cgroup limits.
The scripts under `checkers/` are the exact original compiler drivers. They retain their historical paths and are not run by `check.py`.

## Source stages

`manifest.json` records each original path, source hash, byte count, line count, parent, and patch.
There are 15 raw source stages, 17 exact strict inputs, and one earlier Audit import table.
The additional 194-line candidate-app draft precedes the 197-line checked failure. Both are retained.
The narrowing draft has no failed compiler check. Its namespace correction was made before its first successful check.

| Stage | Lines | SHA256 | Recorded status |
| --- | ---: | --- | --- |
| `factory-private-258` | 258 | `4ecf2348ac8dec0330c7fabfc0383c88bfabf3268a02feed5177d27a1b324ba4` | strict-pass |
| `factory-public-259` | 259 | `282eb82d58fd62cda60a3d5c86ade4a12d61a461075721eb3639be336ac4a311` | strict-pass-public |
| `initial-draft-148` | 148 | `022cd270da57d3fb7197653bf17d8f117e433e6fb1fceb30f60be7d182a8e7e7` | strict-failed-check1 |
| `initial-repair-150` | 150 | `8d8769086daa78392bf9ea4c9ee30dccd34878382f165272149ab735f029631f` | strict-failed-check2 |
| `initial-checked-150` | 150 | `fd9f2ece1f7fa5706f821fd02bce19c95a0a751b8238fca155008856923ece21` | strict-pass-check3 |
| `initial-public-209` | 209 | `91518afafd9b1af39985334fac41dd27b94d4580566fbbac7d0a8a91dcddb0d0` | strict-pass-public-two-laws |
| `narrow-draft-102` | 102 | `7d3f1c82ba2025dca6602d4444e947db7b9124022931d247b16123e5a57605ae` | uncompiled-internal-draft |
| `narrow-checked-102` | 102 | `95bc5dba274689a1d2e0808862f2f8adcc5bd6df218d992ae567acf9360bd76a` | strict-pass |
| `narrow-public-103` | 103 | `432f1de3c5a6c3195ba4618f86d31bcabccfcba746cc31605617f42f906442e5` | strict-pass-public |
| `candidate-app-internal-194` | 194 | `6bfb11fc93162b14a2881575868686decf21cfbb28a672a96ac110d8a0159791` | uncompiled-internal-draft |
| `candidate-app-failed-197` | 197 | `1f5a6b889f01b25ab0da412aec92cc9340994632cfdfe21b350bc8130b00adf4` | strict-failed-check1 |
| `candidate-app-checked-255` | 255 | `b1fdc30e04ee5c8b11a9969a4de62e31b5ae38a0c4e61417860c20cc7dea068a` | strict-pass-check2 |
| `candidate-app-public-256` | 256 | `e1ffee9271761f7aca78fb32d146b73eabf085d62108c7850d7b31c73a7ee5a3` | strict-pass-public |
| `candidate-roles-failed-55` | 55 | `b0681ea6816cbfacd6c92f04174b0d2fa5576804eb9886fba78af554d3bc8e95` | strict-failed-check1 |
| `candidate-roles-checked-63` | 63 | `2af0da30f84c8300e961a625ccfedd13ec695ba8e517888fe1df3dc66d1c461a` | strict-pass-check2-private |

The seven bases and 26 ordered patches reconstruct all 33 stages.
The public 209-line interval stage includes the new `current_narrowed_filter_interval` composition.
The candidate-role helper remains private. Its failed and successful exact inputs are retained.
All captured headers, pins, repair patches, draft notes, and receipts remain byte-exact under `metadata/` and `headers/`.
Historical notes can say “uncompiled”; the later checker reports record the actual outcome.

## Captured checks

The ten focused checks contain six passes and four failures. Their exact inputs are reconstructed separately from raw source.
The failed source stages preserve their diagnostics, including compiler recovery axioms. The passed stages use only standard axioms.
The private checker script is stored once because its bytes are identical at all ten check locations. The manifest retains every original path.

The original public checker completed the full Audit build and the factory and narrowing strict checks.
It then failed while printing interval axioms under a namespace that differed from the source namespace.
The source namespace is `MicroCFTA.SourceSynthesisCurrentFirstFilterSourceLink` for both the interval and candidate-source modules.
The repair changed the instrumentation names. It retained the same completed first three checks and the same source tree.
Both exact public checker scripts, all actual strict inputs, the failed partial report, and the final report are retained.

The final report records seven successful checks, 5906 modules, 4904 Audit imports, and 94990 audited theorems.
The exact source-pin table has SHA256 `4e8747d86eff84ad56ebd3ae4bec7b49a357281b2042003b2d1c4272c451450c`.
It binds the four public source stages and the exact Audit input to that same source tree.
The large pin table stores hashes, not source snapshots. The Audit base is the actual import-table input, not a build archive.

## Scope that must survive restart

The public laws establish current source factory operands, the actual initial source-build interval, first narrowing row inclusion,
and the stated candidate-source origin observer. They retain complete row guards and actual ordered build endpoints.
They do not establish that the nonshared native Parent receipt occurs in the eager shared driver.

The 97-line audit under `audits/shared-scope-correction/` is critical.
The first eager entry is `runPrefix` then `OuterNarrow` then `SelectedPreparation` and `CachedOwn`.
The historical first-filter Parent observer uses a NONSHARED Parent worker. The eager terminal checker uses a SHARED worker.
No receipt cast or root-specific Parent call follows from initialization or from these source laws.

The 48-line header and 70-line plan under `audits/PLANNING-ONLY-prefix-origin/` are unproved planning artifacts.
Their next step is to invert the SAME successful first prefix and preparation and connect actual scan membership.
They must not be counted as a checked API, an eager provenance theorem, or a completed driver attachment.
This packet proves no finite Type witness, satisfying assignment, output existence, survival, typing, or whole default completeness.
Identity membership remains a separate positive case. Later app edits require their own actual history argument.

`replay-checked.json` records the source-only replay performed during assembly.
`SHA256SUMS` covers all packet files except itself. The manifest preserves the detailed source provenance.

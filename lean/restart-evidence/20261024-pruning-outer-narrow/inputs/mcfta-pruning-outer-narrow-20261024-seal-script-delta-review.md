# Outer pruning seal-script delta review

SOURCE-ONLY DELTA CLEAR at 2026-10-24 07:31:01 CEST. The full current verifier was read: 221 lines, 12944 bytes, 89 assert nodes, SHA-256 a9d247255cdc5f16f96660f94b7ec0cf923c29a411473a80cbaabe032d06ff38. I reviewed the complete retained prior verifier, the exact three-hunk patch, the setup record and its complete six-artifact receipt, the actual driver, and the body gate. No prepared script, compiler, Git/network or board action was executed. Only this separate review was written.

The earlier seal-script review remains unchanged at SHA-256 2804c05a202fb8fa826c0de07f357293062f707a865dafa7e0154b94b7946cde. It missed the distinction between literal STRING contracts and STRING digests. Its description of those contract entries was incorrect. This addendum corrects that finding and reviews the retained setup failure. It does not rewrite the earlier report or classify the failure as a Lean attempt.

## Literal contract correction and gate

The seven contracts.json values contain complete literal Lean fragments, including their final newlines. They are not SHA-256 digests. The new loop requires `isinstance(literal, str)`, compares `payload.decode() == literal`, and requires the literal without trailing LF to occur exactly once in the production source. The complete map must equal body-gate.contracts. All seven literal values are nonempty and independently match their exact payloads and gate entries.

This retains the separate cryptographic checks: each payload still has its actual bytes/SHA in the complete 53-entry pins map; pins.json must have the frozen pins hash; and the whole FROZEN.json hash must equal body-gate.frozen_sha256. I checked the actual gate bindings: frozen d742fa145205d8d29f92edb303e2d1a5f83064d85d33cd69b01253a3acec3b16 and pins 4ca506dea1d6a6b4691137ad0dbf5622b1bdc668f047804e41b6632b70ac8982. Both match the unchanged owner. The gate records ROOT_ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY and compiler_invoked=false; its mathematical_body_exists=false describes that gate's own pre-body cut.

The contract change fixes the representation mismatch. It does not remove hashing, alter a frozen header, add a premise, change a mathematical body or weaken the exact owner/source identity checks. I independently reconstructed the complete new verifier from the saved old source using only the three patch blocks; every other source byte is unchanged. The archive/documents/publication scripts also retain the exact hashes from the prior review.

## Setup failure classification

setup-failures.json records the ordered setup errors: the gate writer compared literal fragments with digests and stopped; the body writer then failed on its missing-gate assertion; the orchestration still launched source-check-1. The source-check-1 cap itself exited 1. Its raw cap log shows FileNotFoundError while reading the absent proposed Lean source at driver line 14.

The retained 33-line source.py is byte-identical to the actual check.py. The failing source read occurs before construction of the source command and before `subprocess.run` at line 24. Therefore this particular attempt did not launch Lean. Its empty target directory contains no .lean input, no compiler raw.log and no report.json. I checked those facts against the actual directory, not only the setup description. The log SHA equals the setup record's 9f8af3d737259eafb24fe8970ac0620704108267f04a8aca940363d7bccc7ce1. The embedded receipt equals the actual top-level receipt, including its command and exit 1.

All six cap artifacts exist: receipt/log/limits/usage/source.py/peaks. Limits are exactly 4 GiB max/high and swap0. The recorded usage sample has age 0 and 89 percent remaining. The peaks file records the small failing Python process; it is not a Lean peak or successful proof result. No source variant or compiler error is inferred from this setup failure. The two uncapped setup assertion failures remain in the explicit sequence rather than fabricated compiler report directories.

## Verifier and retention effect

The new setup branch requires compiler_invoked=false and exactly source-check-1 in the capped setup set. That set must be disjoint from the dynamic actual Lean report set. It also rejects any compiler report/raw log or Lean input beneath that setup directory, and checks its retained cap log hash. The existing exact report-directory set, actual source/input hashes, selected empty strict log, all-linter/default source checks, five complete public types/axiom map and actual build-log gates remain unchanged.

`receipt_stems` is now baseline-1 plus the separate failed setup cap plus actual Lean attempts. Both limits and usage stem sets must equal that complete set. Every stem still needs all six artifacts, the exact cap and fresh usage. The receipt exit check includes the setup set in the required failed exits; the Lean report exit check is unchanged. Consequently `lean_attempts=len(expected)` excludes setup source-check-1, while `resource_receipts=len(receipt_stems)` includes it. Keep the future build-summary attempt/failure lists for actual Lean invocations; source-check-1 is a separate setup record and cannot be reused as an actual compiler attempt.

The reviewed archive copies the whole area, so it retains setup-failures.json, the full prior verifier and patch. Its prefix input capture also retains the complete setup cap family and this delta review. The active archive-1 exclusion is unchanged. Baseline preservation, nine exact document inverses, the additive Audit import, FINDINGS repair index first, full owner controls, prior narrowing publication records, exact local FS/index/HEAD checks and ordinary singleton-destination formalize publication remain as previously reviewed.

Actual successful source/public/build/Audit/proof/document/seal/publication outcomes are outside this delta's scope. This is clearance of the source correction and actual setup-record classification, not a runtime seal or proof receipt.

## Exact reviewed inputs

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| `/tmp/mcfta-pruning-outer-narrow-20261024-verify.py` | 12944 | `a9d247255cdc5f16f96660f94b7ec0cf923c29a411473a80cbaabe032d06ff38` |
| `/tmp/mcfta-pruning-outer-narrow-20261024/verifier-before-literal-contracts.py` | 12304 | `e523ed61d67f292ed2861461e29348be86819a0cf73011f0016f8bcb9595259f` |
| `/tmp/mcfta-pruning-outer-narrow-20261024/verifier-literal-contracts-setup.patch` | 2359 | `68a2aff4b59128404bd5b52a1d72df5c896bd406f0f4c7699bd88a175ac81a58` |
| `/tmp/mcfta-pruning-outer-narrow-20261024/setup-failures.json` | 1936 | `4adc5e99b63db3db3063d6b673f75ea2fc9aba8826149447c262a142c111ec31` |
| `/tmp/mcfta-pruning-outer-narrow-20261024/body-gate.json` | 4127 | `e600eed61a06e0ea8709f825d0049745766b24db3866211949e02de5f7280c58` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-proposal/FROZEN.json` | 970 | `d742fa145205d8d29f92edb303e2d1a5f83064d85d33cd69b01253a3acec3b16` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-proposal/pins.json` | 7261 | `4ca506dea1d6a6b4691137ad0dbf5622b1bdc668f047804e41b6632b70ac8982` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-proposal/contracts.json` | 3254 | `78616572a7fd9efa1c4d85a033d8e30c36e8527fff62c4e330170a2ddc393740` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-seal-script-review.md` | 14001 | `2804c05a202fb8fa826c0de07f357293062f707a865dafa7e0154b94b7946cde` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-source-check-1.json` | 793 | `7c9f4fc040b6935f0b2a9766b950664a5c13206b06122fcaf3ded92feea9c64f` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-source-check-1.log` | 678 | `9f8af3d737259eafb24fe8970ac0620704108267f04a8aca940363d7bccc7ce1` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-source-check-1.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-source-check-1.usage.json` | 114 | `d2466edfa14332ed70ca76fe020e7ee9488c5ce8cef4fdea01160499e1bc16ca` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-source-check-1.source.py` | 1628 | `c0cf4bf0fbe672e3b63fc3f1fb80805ec66c88364ca811f1bec7709982df4e5d` |
| `/tmp/mcfta-pruning-outer-narrow-20261024-source-check-1.peaks.txt` | 37 | `363b2f34e4aa5ed9144113e067d4f3a14aeb4e41d700f28aa6b76e7b9f9b1a99` |

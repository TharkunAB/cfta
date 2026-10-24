# Own-arity: supplemental failed-seal repair review

Review cut: 2026-10-24 12:18:07 CEST. SOURCE_AND_RETAINED_DATA_CLEAR for the exact archive89-line/verifier228-line sources below. I read both current programs in full, both exact patches, the complete failed result/ref-delta/cap log and repair note, and independently checked every one of the retained196 manifest payload hashes. No blocker was found. This is static rerun-source clearance, not a successful second-seal or publication result. Original script/public/document reviews and all earlier artifacts remain immutable.

## Failure and precise policy change

archive-1 is a REAL exit1. Its saved verifier failed at rev-parse of an expired `refs/codex/turn-diffs/captures/.../base` reference; the underlying Git command returned128 and the archive driver then exited1. This was after archive creation, not a Lean failure or a successful seal. failed-seal-result-1.json retains the complete stdout/stderr and exact manifest identity. The external cap log retains that result plus the driver AssertionError.

The retained delta lists THREE missing refs and THREE new refs, all strictly inside `refs/codex/turn-diffs/`. I checked every missing ref/value against baseline-refs.txt. The only recorded changed project ref is the already-expected `refs/heads/formalize` movement from baseline7c940534 to2829c12a832e7214642804d6e5cac7cbda788271. I inspected saved data only, not Git; the eventual verifier must still check the real repository.

The new fixed-ref predicate adds ONLY `not ref.startswith('refs/codex/turn-diffs/')` to the existing formalize/origin-formalize exclusions. Branches, remotes, tags, backup refs and other Codex namespaces remain subject to the old equality check. No ref is recreated/deleted or branch rewritten by these scripts. Baseline refs and the observed delta are retained. This narrow exclusion addresses transient app bookkeeping, not source/proof/project-ref preservation.

## Exact retention and ledger

The moved first archive has196 manifest payloads/197 physical files and exact manifest SHA `8532743686e110919b24981caedc9fe790e7e56b8a85784ebb3bbaa4c8ac0d4d`. I checked safe relative unique names, every payload SHA and the COMPLETE physical file set excluding only its SHA256SUMS. No payload was lost or changed. Its old verifier equals pre-seal-repair-verify.py, and its work/build-summary equals the original pre-repair summary. The new outer manifest will include that entire nested failed archive, manifest and all controls; the additive inner loop rechecks all original listed payloads.

Current build-summary changes ONLY by adding `failed_seal_attempts:['archive-1']`. Its six Lean/Lake attempt names and the two actual failed checks strict-1/public-1 are unchanged. The failed seal is therefore a SEPARATE metadata/sealing attempt, not an extra compiler job or first-pass claim. New receipt_stems = baseline + those six attempts + archive-1 gives eight pre-rerun families, each retaining all six suffixes. The added expected status is1 for archive-1; all existing compiler failure/success predicates remain.

I checked all six actual archive-1 cap artifacts exist. Its source.py equals the ORIGINAL reviewed5245B archive source. Cap exit is1, memory.max/high4294967296,swap0; recorded launch usage age0/84percent and peak283M. These are historical receipt values, not current usage. The new archive excludes ONLY its own active archive-2 family. It now includes the failed archive-1 family, both original scripts, both patches, ref delta, failed result, repair note and this separate review through the current-prefix input/area copies. The active archive-2 receipt remains a later checkpoint's custody obligation; no unfinished receipt is claimed complete.

Production source, body gate, proof metadata and note match the exact retained first-archive bytes. All nine current document hashes still equal the same unchanged document-changes after hashes. The source remains93 lines/e6b77f43df9a58280c3d8bfd3615e8f390c1d0785d49257817ecb1387185e519. This repair adds no theorem/compiler/proof-limit/native change and does not rerun a proof. It preserves complete131256 baseline blob/mode checks, nine inverses/Audit, frozen owner/contracts/source identities, public readback/axiom subsets, resource limits, project refs and publication guards.

The archive's added INDEX paragraph truthfully records the failed first seal and app-ref exclusion. The repair note preserves the separate70-versus71 split-entry citation correction as source metadata, not a failed compiler attempt. No source identity or mathematical conclusion changes. All goal/H6/open native boundaries remain unchanged. The original reviewed documents do not gain a premature seal/push claim.

## Exact input pins

All paths below are under `/tmp/mcfta-pruning-enumeration-own-arity-20261024/` except current scripts, which are its external `-archive.py`/`-verify.py` siblings.

| Object | Bytes | SHA-256 |
|---|---:|---|
| current archive.py |5612|`6039e6d2631d92cb2d582e93a1ee7e98904be634e2562e08b9f5385adf41ab1c`|
| current verify.py |13803|`168541c88d20d3cf70782300e2af1982697442ddc172c348f594b4a144999431`|
| pre-seal-repair-archive.py |5245|`f4e5acc5c4d61e208530e6b4bdbfbf03da21dd6c30840a86637decc5104b59d8`|
| pre-seal-repair-verify.py |13233|`d5f0a42792f0a1b9004c5c4815658433c7c67f65d045b8edba130dae2405c8e0`|
| archive-expired-turn-refs.patch |1397|`e296bc047e8c74880cc5eee63898a97b64bcf116ac587b915d05deca3c9359ad`|
| verifier-expired-turn-refs.patch |2238|`99280382d820f4eb829ffbac0879c1a1dd0cb665b6d732fb3f8f0e6311d43091`|
| failed-seal-result-1.json |1491|`a16d1f0415ae6514c814b53df5405219b97b8e55f27553f5fecbf221012d4ee2`|
| failed-seal-ref-delta.json |1167|`afa1d07204b1a508f89f42dcc482a5d8bd3d705c3430cf582111192d631d8344`|
| seal-repair-note.md |1721|`35948a3e4586b0aa40ed155d0961c85d1c721d8268f1eeab2aa5df7e53d8d1de`|
| pre-seal-repair-build-summary.json |1153|`3ce38049cc89f84c72a4d732f0fef3032808c6940e31a724cd3176a9413d2c15`|
| build-summary.json |1202|`3210c0d773b588ff941fe747c190bb9b176f3316d5bda06a66860b0d9d5828e5`|
| archive-1 cap .json |600|`a04ef6af4bf56c8281b58ec225a9b93d3598659ade795e6f43553895b9530930`|
| archive-1 cap .log |1701|`feb5e22261724c7874df6b011f39ac5e73ee8afdd81bb095efe813c478fcdc3c`|
| archive-1 cap .limits.json |90|`408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3`|
| archive-1 cap .usage.json |114|`c4547dd20f4ca0704d574d110138a5047dff61c1fb2c8fb04bb8972c7363cc60`|
| archive-1 cap .peaks.txt |38|`861400fd72736e2e1482d2b56500bfe4f8110efb3a587b6001327261ddb4fec5`|

The two patches independently reconstruct the current full scripts byte-for-byte from the originals. I wrote ONLY this new immutable report using source/data/hash/JSON/diff reads. No prepared script/import/parser/compiler/Git/network/board or repository/owner/previous-report mutation occurred. Root retains rerun and publication responsibility; no future success is inferred.

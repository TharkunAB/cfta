# Derived scalar node-view name repair review

Status: CLEAR. Recorded 2026-10-24 03:41:48 CEST; inspected working diff against HEAD `2c8b42421d0f395141a00fdc172a4660acebd9ba`. Independent read-only review of Root's Haskell repair and actual saved native validation. No compiler, prepared program, repository edit, or new test run by this reviewer.

The change is minimal and fixes both reproduced invalid-name paths. No further correction is needed for this scope.

## Source and scope

- Whole producer `cfta-th/src/Data/CFTA/TH.hs` (76 lines) and whole test module (136 lines) were read, with the complete five-file diff. `generatedName` is shared by type-name generation (48) and every constructor (58). The new guard at 69 rejects a trailing `#` before appending `Node`, lookup, or `mkName`. It retains the existing splice-time failure path and caller name in the diagnostic. A valid MagicHash source identifier such as `Hashy#` would otherwise produce the invalid middle-hash identifier `Hashy#Node`; the same applies to `Constructor#Node`.
- Runtime source delta is one `Data.List.isSuffixOf` import and one refusal. Generation for accepted names, constructor order, field counts, fresh child parameter, generic derivation, NodeView instance, namespace collision checks, and all other refusals are unchanged. No new dependency or public type is introduced.
- Existing refusal regression gains two MagicHash declarations (81–85) and two `recover` entries (129–130); expected length changes five to seven. Each entry returns false if `deriveNode` itself accepts the declaration, even though its returned declarations are discarded. Thus the regression specifically checks early producer refusal rather than relying on GHC rejecting emitted syntax later. This is appropriate for the bug.
- Haddock, README, design-note refusal list, and changelog consistently document the extra unsupported name form. Comments use the existing style. No handwritten view, generator semantics, accepted source constructor, Haskell core, rank/count implementation, or unrelated Amount declaration changes.

## Actual red/control evidence

The plain-name Control module compiles with exit 0 and an empty log on the old producer. The identical-source control also passes after repair. Its source SHA is `6cd531996ad3cae9c5007349e79b8b00372ad8f557082dcd78b2be8e3f241651`.

Old native constructor probe exits 1 with GHC-55017: `Illegal data constructor name: ‘Constructor#Node’` (`native-names/MagicHashConstructor.log`, 344 B). Old native type probe exits 1 with GHC-55017: `Illegal type constructor or class name: ‘Hashy#Node’` (`name-regression-red/0.log`, 349 B). These are valid source declarations under MagicHash; their generated names are the defect.

The retained old producer `name-regression-red/TH.hs` equals the complete HEAD producer byte for byte. The retained regression Spec equals the current test module byte for byte. That red run passes the other three examples and fails the refusal example with expected seven true values but actual `[True,True,True,True,True,False,False]` (1722 B log). The two new cases therefore distinguish the old producer.

Repaired native probes deliberately exit 1, now with GHC-39584 and the intended early diagnostics: constructor `deriveNode Hashy: names ending in # need a manual node view` (223 B), and type `deriveNode Hashy#: names ending in # need a manual node view` (226 B). These are expected rejection checks, not failed validation jobs. The producer's generic diagnostic mentions the source datatype in both paths, consistently with its pre-existing unsupported-feature messages.

## Actual green checks and retained interruption

Root's repaired `cabal test cfta-th:node-views -j1 --ghc-options=-Werror` run passes all four examples, including all seven recover cases. It runs in nix-shell with GHC 9.14.1 and explicit single-worker/1 GiB test RTS limits. Fourmolu check passes for both changed Haskell files.

The first validation driver then stops at ordinary `hlint cfta-th/src cfta-th/test`, exit 1, solely for the existing `Use newtype instead of data` suggestion on unchanged Amount (41–43). This diagnostic and all earlier passes remain retained. Root continues only the remaining checks: `hlint --ignore-suggestions` passes with `No hints`, cabal-gild check passes, and package `cabal check` passes. The CI uses `fail-on: warning` (ci.yml 42–46); ignoring suggestions retains warnings/errors rather than suppressing a new repair warning. Amount stays unchanged, which avoids an unrelated strictness change. No earlier passed suite or formatter was rerun by that continuation.

All 13 saved command records were parsed and correlated with their exact log bytes/hashes. The expected rejection diagnostics were checked in their raw logs, and both available native source hashes were verified. The report does not claim a fresh full repository test run or fresh repetition of the design note's older standalone validation paragraph.

## Evidence identities

All paths below are exact inspected files at this cut. Hashes cover full raw file bytes.

- `/home/tritlo/Code/mcfta/cfta-th/src/Data/CFTA/TH.hs`: 3331 B, SHA256 `4e3d0515d27c97743824c3a99cd77b920034116ff17d909d01b12c2f47e60a69`.
- `/home/tritlo/Code/mcfta/cfta-th/test/Spec.hs`: 5266 B, SHA256 `e1dfea241a62836d5cdcbbb73059d4726cf7575937a54a4464bc84c9413b4ffb`.
- `/home/tritlo/Code/mcfta/cfta-th/README.md`: 2266 B, SHA256 `df5a2578d0cd201ec8cd318f805ba7bd2a5911ff439a77de8ecbbc4a6b758897`.
- `/home/tritlo/Code/mcfta/cfta-th/CHANGELOG.md`: 191 B, SHA256 `3d087be057f38d52da6851b185718715016345cfbffa7e2592850dba9850cdc0`.
- `/home/tritlo/Code/mcfta/docs/generated-node-views.md`: 3197 B, SHA256 `1134f05305781a879992cb4e3d475a873fb067f1c226f9d81140871c543bd33a`.
- `/home/tritlo/Code/mcfta/.github/workflows/ci.yml`: 5205 B, SHA256 `ed3ccf93847129ed42222ca2efc8895209129f2168be70e43aee004cda0178f4`.
- `/tmp/mcfta-derived-scalar-shape-20261024/native-names/Control.hs`: 160 B, SHA256 `6cd531996ad3cae9c5007349e79b8b00372ad8f557082dcd78b2be8e3f241651`.
- `/tmp/mcfta-derived-scalar-shape-20261024/native-names/Control.log`: 0 B, SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/mcfta-derived-scalar-shape-20261024/native-names/MagicHashConstructor.hs`: 174 B, SHA256 `b62a7edcf32b598678eef4577589a69cf5991a4c7bd3208d24b1f9313362f557`.
- `/tmp/mcfta-derived-scalar-shape-20261024/native-names/MagicHashConstructor.log`: 344 B, SHA256 `69590f65676c9c2f85a119a8631a091b64e698e49332462b52a09637e3c34519`.
- `/tmp/mcfta-derived-scalar-shape-20261024/native-names/report.json`: 1125 B, SHA256 `152f364accfd949d89a164c4ba8a73c7aa0c2900da03d044b2aa43520843a853`.
- `/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red/0.log`: 349 B, SHA256 `f5dc9030e4cbeaa7916c79da525378de43c72948081a7c53be5fd721838278be`.
- `/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red/1.log`: 1722 B, SHA256 `ae927364419f835fef5569a7dca16045f2b76c59fccaf1d817179dff00f70137`.
- `/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red/MagicHashType.hs`: 168 B, SHA256 `c808588a400b10300ba8e7381ff284ec756bb059a88b2d0ff693e060a1238ebe`.
- `/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red/Spec.hs`: 5266 B, SHA256 `e1dfea241a62836d5cdcbbb73059d4726cf7575937a54a4464bc84c9413b4ffb`.
- `/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red/TH.hs`: 3196 B, SHA256 `f1c7b9a41f6f897a6ecf1ba7e17afadef4622d94c26c12a02f1d7f5252ac6105`.
- `/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red/report.json`: 803 B, SHA256 `d0dca7ce07027d818200b02d55bf9af5b3200709180a32ca977006844f759ab5`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green/validation-0.log`: 1861 B, SHA256 `54a3ddf42a8f93974c63e5b0a2191dd12d9d806b3d4d119000cf79fb3da2253e`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green/validation-1.log`: 58 B, SHA256 `5e9ce55055974291cc141f348aff187d72f3871a1662a95af93deb2dd7341175`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green/validation-2.log`: 339 B, SHA256 `db3bc19f084c6d64ebeb5a59a52b5035c89c8f0a01fe9b099343c528ccbde3ee`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green/validation.json`: 846 B, SHA256 `e0113cd5b97093c8e001d11afe044d291131a52b91ca9433b1a56207202f4fbe`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/probe-0.log`: 0 B, SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/probe-1.log`: 223 B, SHA256 `7337263a05372e4f19ce4951aa4245ec78968a2e5eae0011316389e610854437`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/probe-2.log`: 226 B, SHA256 `199e77f8c974e22a84fcb3d4aa8820ea5c537fd6bbeee52c7616d2ab37c6662c`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/probe-reports.json`: 1546 B, SHA256 `64269ea590a25369ece1ecd8cb4410d1438bb92181e20625e5e92923774557dc`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/validation-0.log`: 9 B, SHA256 `3ad781d618c325a4232d57cc2d042c8bc78de184f9fc851181cf789e52f3ef09`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/validation-1.log`: 0 B, SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/validation-2.log`: 53 B, SHA256 `a19b4064f1acadadad1e1f24beae3785b778a6c5baabde7f333e4dacb7191d30`.
- `/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest/validation.json`: 742 B, SHA256 `37e253c0778cb329beff2b0a67956acf374e7f98f8d76e87e987418dd7fd825a`.

# Independent main repair integration and document review

[2026-10-24 04:24:52 CEST] CLEAR. Source identities and final document claims match. Root must still create and verify the evidence archive and seal before publication; neither seal nor push was observed here.

I read the complete five-file upstream diff, all final nine-document diffs, the complete43-line focused note, the complete replacement FINDINGS handoff, and the baseline/merge/native-pin metadata. I used read-only Git and source comparisons. I ran no compiler, native probe, prepared program, Git mutation or repository edit. Unchanged proof bodies were not reread.

Verified commit identities:

- Previous imported main:c4f7319acf84213fccc8ea389487d4176e4f0b62.
- New main74250bd889685da436cdbfe32ac4b5a0878ffd09 has exactly parents c4f7319acf84213fccc8ea389487d4176e4f0b62 and f1f266ab4108131a01b9a28577f91de67b98eeb3, and records PR172.
- Integration ea9965949bdad994709318cf54162bea1c23cf40 has exactly parents ed89dccbf8242231cde1abf87e52f909cb726470 and74250bd889685da436cdbfe32ac4b5a0878ffd09.
- Integration and previous pushed baseline have identical COMPLETE Git tree2cdfb28f9d8972d3507953a1434d42c1d0f7992a. New main's complete tree also equals its cherry-pick parent's tree.

The upstream delta has exactly the five paths below. For each path, the mode, Git blob, byte count and SHA256 are equal across local repair07229ca7f3208385a52c442965d8f2dcf73f7d99, upstream cherry-pick f1f266ab4, new main74250bd88, previous pushed ed89dccb and integration ea9965949. Current working files match. All five modes are100644. The retained5318-byte main-delta.patch equals the actual complete old-main-to-new-main diff.

- cfta-th/CHANGELOG.md: 191 bytes, SHA256 3d087be057f38d52da6851b185718715016345cfbffa7e2592850dba9850cdc0.
- cfta-th/README.md: 2266 bytes, SHA256 df5a2578d0cd201ec8cd318f805ba7bd2a5911ff439a77de8ecbbc4a6b758897.
- cfta-th/src/Data/CFTA/TH.hs: 3331 bytes, SHA256 4e3d0515d27c97743824c3a99cd77b920034116ff17d909d01b12c2f47e60a69.
- cfta-th/test/Spec.hs: 5266 bytes, SHA256 e1dfea241a62836d5cdcbbb73059d4726cf7575937a54a4464bc84c9413b4ffb.
- docs/generated-node-views.md: 3197 bytes, SHA256 1134f05305781a879992cb4e3d475a873fb067f1c226f9d81140871c543bd33a.

The repair still rejects a trailing # after the uppercase test and before either namespace lookup. Both type-name and constructor-name regression cases remain in the existing suite. The literal nameBase++Node rule remains unchanged. The source/package/docs and their tested context already exist in the previous complete tree. Repeating those successful checks would not exercise a new input. The note correctly describes prior validation as retained, rather than newly executed.

I separately verified unchanged installed and committed Positions, RecordTypes, GeneratedNodeViewShape and Audit bytes. The full equal-tree comparison also preserves every other committed proof/evidence path and mode. Positions retains SHA f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d; RecordTypes c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf; GeneratedNodeViewShape bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9; Audit57c78dbe05d0facbd6350b1011eb97f57918e205f31d0cee6abbd328358ea9ad. Retained Audit3678/76071 and40-signature/32-axiom results are the earlier results, not a new run.

All nine identical insertions are22 LF characters/1178 bytes, SHA25665dcc55fcd370d0353ebb66ecd25404e31577467e29706d00e3aa49e475cf134. Each current insertion matches its recorded offset and after hash. Removing it recovers the exact baseline bytes in eight files. For FINDINGS, removing the insertion recovers the declared handoff replacement; reversing that one declared replacement then recovers the entire baseline FINDINGS byte for byte. Every recorded before/after hash matches. The first five repair rows are byte-identical. The sixth row, summary and external action now report the actual upstream merge. Historical failures use original-producer/past-tense wording; their witness details and validation remain. The complete repair index remains FIRST, before the new status block.

The installed focused note equals current-note.md. It keeps H6's actual covered-construction/cache/history/empty-payload scope and exclusions. It does not enlarge H6 or claim native extraction, general pruning/order laws, practical width/resources, typedTypes composition or convergence. H23 remains queued and the full goal active. No additional external patch is needed for the six recorded repairs; that statement does not close general proof obligations. The new prefixes explicitly precede evidence creation and authorized push.

The archive destination lean/restart-evidence/20261024-th-repair-main was absent when checked. The note describes the verifier's intended127926-baseline-file preservation scope; this review does not certify a future successful full preservation/seal run. Root's final archive verifier must retain the current exact inverse metadata and all earlier sealed evidence before publication.

Checked report inputs (SHA256):

- baseline.json: 420 bytes,c7b39ef61f4ebdd0caccecd62254f3539054a055b3e158c872c9d3b28394cf11.
- merge.json: 291 bytes,a44c0aa8def52613b6ea87901bf4289dca608928a97d92cadeae1f846581666a.
- native-source-pins.json: 679 bytes,376d5c76c52be1a38bf01c6b5fe81de886534941c271f989e08e7635f3690884.
- main-delta.patch: 5318 bytes,ceb143eefb2208f3340548d1a89c664ad71fa43629b7fdd062f607aedaf33338.
- document-changes.json: 13133 bytes,a40cc123512be40a9a26ce76ed2660c9a4269773b7adbc8975af03b5ac87ce3a.
- findings-index-change.json: 8104 bytes,3ad757afaef8a289751cf722a50c347ae99a7072a912102cf5639ce618f148c9.
- current-note.md: 2746 bytes,bf0a656a3d4db73601a22a5dcb8538f8357f7cbe12ccbbc2c66e9edbdc5beec8.

Current nine-document hashes:

- NEXT-PROMPT.md: d56ae844f468cbb24023200244c2ffe62150e56189f11587f23a9a38e1be9a93.
- HANDOFF.md: 3e1447e39e171665b30b68fc80c0111fcd8860fbbc40468a5476e5db2cefa961.
- FINDINGS.md: 715e92355bb54b3d3e5475ef9375885117eb29be7b331ffa73ad13ba41c6cfc7.
- lean/README.md: 15a0cd929f68cea79600bc6dff82cf6bb9dc9e0902a40fbfe97a226da3d1ca34.
- lean/SYSTEM.md: fdbb7587cfd38c9105b0277b9c7d6c9bcd401d3676e92c614f7aaa913645deb2.
- lean/API-COVERAGE.md: 2907f61e2cbdfc6593eb6869f1a0087c187791440a11a9b1488af6af4aeb93c5.
- lean/COVERAGE.md: 975f8e7c206f76639d5992d3f102bfde727e762ad2ae448a8a23efbe40a65526.
- lean/notes-proof-status-20261017.md: 2c239f7227252000d08c0df9fe63a0a78da00fdea2ad8156cbf3bba1703adc36.
- lean/notes-current-system-claim.md: ff13f55e1f53abaf3c8f1296cdfd90fca1e5a8a6bbd9ae80acc4226d68b48fb6.

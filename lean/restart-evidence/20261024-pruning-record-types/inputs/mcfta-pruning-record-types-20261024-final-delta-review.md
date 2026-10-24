# Final helper and callback delta review

[2026-10-24 04:10:31 CEST] CLEAR. No source correction is required for the reviewed final deltas. This is an additive source review. The earlier helper and callback reviews remain unchanged. Required authored the helper. Root made the selected repairs and owns compilation. I authored neither selected module.

I read the complete final helper, the complete d550-to-final and structural-to-final diffs, the complete callback proof diff, and native Pruning.hs147–213. The callback review reuses the earlier complete source read plus this exact delta. I compared all 22 helper and all 10 callback theorem statements byte for byte. All statements and declaration order are unchanged. Both selected files equal their respective successful compiler snapshots.

The helper change from d5504f3e unrolls only literal finite folds and maps. The app branch is exactly annotation-true(marker-true(function-false(argument-false(types)))). The non-app four-child branch uses the same right-associated all-type fold. The non-filter two-child branch uses annotation-true(term-true(types)). The renderer replaces the corresponding finite maps by lists in the same child order. Matching the fallback list as `children` binds the same matched list; it does not add a branch or change a recursive argument. Both sizeOf measures remain unchanged. The complete programHoles definition is byte-identical to d5504f3e. Exact full-label app/filter tests, raw hole IDs, duplicates, and malformed-shape fallbacks remain unchanged.

Relative to the structural check4 snapshot, all executable definitions are byte-identical. Exactly three helper proof bodies change: typePositions_type_node and openProgram_type_node rewrite the definition equation before reflexivity; programHoles_type splits hole/node and rewrites the node equation. All other helper proof blocks are unchanged. These repairs do not change hypotheses or conclusions.

The callback executable prefix is byte-identical to the reviewed 55e14113 source. Exactly two proof bodies change. recordTypes_metadata splits the actual empty/nonempty catalog branch before applying the same successful-bind/pure equations in each branch. recordTypes_transport uses simp-only rewriting of recordTypes_empty under the existential goal. The callback still skips the oracle for an empty catalog; every Left invokes typePositions with isType selected by incoming raw-ID membership in incoming types, so false-position app/filter/fallback fragments can still add type IDs; Right retains types, and both input branches preserve openHoles/typing. No desired-success, canonical-current, or new oracle premise is added.

The observed positions-check6 and callback-check2 reports both record exit0, an empty raw log, warningAsError=true, linter.all=true, and the exact final source hashes below. I read these existing records. I did not execute a compiler or selected program. Earlier nonempty logs and source snapshots remain under positions-check1–5 and callback-check1. No failure was rewritten as a successful job.

The prior boundaries remain: ascending Nat-list set extraction requires its native IntSet correspondence; decimal rendering and native Int bounds are separate; these helpers do not prove native state extraction, global canonicality of arbitrary input lists, or pruning soundness.

Checked inputs (SHA256):

- Final helper: 209 lines, 11125 bytes, f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d.
- Prior helper check3: 201 lines, 10985 bytes, d5504f3e508afd8d1eab5619bcf78b6693733dae8918f26de3c7e531d47ab605.
- Structural helper check4: 203 lines, 11034 bytes, 351400d7c9c96fa5590c3147d9d9b37addd8a5b4ffa4c82a816615a4bda4e41d.
- Final callback: 209 lines, 13138 bytes, c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf.
- Prior callback check1: 207 lines, 13088 bytes, 55e14113e0f51acf8dedebcb066ff4af7d04cbaa46d9329b263de3045922cf74.
- Native Pruning.hs: 16989 bytes, 5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61.
- positions-check6/report.json: 643 bytes, 8743ad5419c131fbbf3b6501a0ecec5df174190f7e71a55125ae20228e3680bd.
- callback-check2/report.json: 645 bytes, a17900ae1eb747c2433fb5aa9be9ad564c2c523c4088778c4be3bba6828b83f0.
- Both final raw logs: 0 bytes, e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
- Unchanged prior positions review: c1fb508c97aaa2860130f37107e6362739b711958322e439bd4e71a0ba29a5b0.
- Unchanged prior callback review: c2e2ffe1045053126133228248bdb2a218cad908e4892940a907b6d66daf2e89.

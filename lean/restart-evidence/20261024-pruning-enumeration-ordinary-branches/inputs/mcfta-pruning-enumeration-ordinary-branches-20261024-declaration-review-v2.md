# OrdinaryBranches V2 independent declaration review

Reviewed at 2026-10-24T17:28:21+02:00. Verdict: CLEAR for the exact V2 declaration correction and associated metadata. This is a source-only clearance. It does not assert that V2 compiles. Root must record a fresh V2 gate before revised body work.

I read the complete V2 delta, affected declarations and metadata, full retained strict-1 input and raw diagnostics, and the new core source cut. I reused the unchanged V1 source review only after byte identity checks. I authored the prior source and declaration reviews. I did not author these declarations or any body, and I did not run a compiler, parser, candidate, import, Git command, network operation or repository mutation.

## Actual failure and correction

The original declaration review missed an expected-type issue at the raw append boundary. The actual first strict attempt failed. The original owner, review and failed input remain unchanged. This report does not relabel that attempt or the earlier clearance.

The strict-1 log rejects explicit `generalizing selected`, because the dependent premise is generalized automatically. It also attempts to synthesize `HAppend` for `ExceptT Error List ...` at the unprojected `consRaw` declaration. The complete 20,184-byte log also contains subsequent proof diagnostics. All diagnostics are retained; the record is not reduced to two errors.

V2 changes the five-line `local-cons-raw.lean.txt` fragment to apply `ExceptT.run` to the left side and both right-side append operands. Thus `++` receives raw lists of `Except Error (result × State)`. The full state, head-before-tail order, match branches and same `before` state are preserved. No new append instance, callback, action or semantic premise is added.

The active core source defines `ExceptT` as the underlying `m (Except ε α)` and `ExceptT.run` as its identity projection. The reviewed lines 128–149 establish this API directly. The correction makes the intended raw-list view explicit. It does not discard errors or change branch effects.

The induction command is now `induction selectedEdges with`. The `selected` premise remains automatically generalized. `before` and all other fixed context remain fixed. The full IH type and the single proper-tail call `ih selectedTail` are byte-identical to V1. No new induction or recursive declaration is introduced.

## Exact declaration and metadata scope

The public context, `run`, `run_complete`, local instance header and every other compiled contract are byte-identical to V1. The public attachment remains plain ` :=\n` for the noncomputable definition and ` := by\n` for the theorem. The only changed compiled fragment is `consRaw`.

The owner retains ten STRING contracts, 52 lines, context six lines and 34 public-header lines. It retains four typed haves, no proof lets, three obtains with 18 fields, 74 scoped entries, one list IH and one restricted call. `obtain-inventory.json` and `case-inventory.json` are byte-identical to V1. The scoped inventory changes only the `consRaw` type and its explanation. The insertion map preserves the nested continuation indentation. The local `ordinaryMonadList` remains a header-only declaration for Root to implement. There is no LawfulMonad, global instance, helper, new carrier, new predicate or added equality premise. The target remains 140–220 lines with hard cap 260.

All twelve changed existing payloads were reviewed: contracts, import routes, induction, insertion map, consRaw, metadata check, proof route, provenance, schema, scoped types, self-review and source index. The 26 additions retain the exact patch, core snapshot/cut, actual failed records, V1 controls and changed-original payloads, delta record and author-only metadata diagnostic. The diagnostic concerns metadata assembly order. It is separate from the genuine Root strict-1 failure and is not a proof attempt.

## File sets, source identities and failure custody

The V2 package has 121 payloads and 123 physical files. I checked the complete file set against relative object pins with both byte lengths and SHA-256 values. Only top-level `pins.json` and `FROZEN.json` are excluded. Nested controls, the historical failed body, raw log, report and draft diagnostic are pinned payloads. Active V2 declarations remain body-free; the retained failed V1 body is historical input data.

The exact delta is twelve changed existing payloads, 26 additions and 83 unchanged existing payloads. All 95 original payloads reconstruct exactly from unchanged copies and `provenance/v1-originals/`. The nested V1 pins and FROZEN are exact copies of the original controls. This is complete reconstruction custody, rather than a claim that there is a separate full V1 directory clone.

All 21 full source snapshots and 30 cuts, totaling 491 cut lines, were checked against their live defining files. The new source is active Lean 4.34.1 `Init/Control/Except.lean`. The existing 15 import routes and 47 defining-source identities remain unchanged. These routes contain 98 repeated adjacent import occurrences and 46 unique adjacent import edges. The new core raw-view API has its own source identity and requires no added project import.

The retained strict-1 input, raw log, report, V1 body gate and prior declaration review each match their actual original bytes. Strict-1 exited 1 under warning-as-error and all linters. No V2 compiler result is inferred from this static review.

## Semantic boundaries

The corrected local equation still describes ordered alternatives from the same incoming enumeration state. The theorem relates every selected edge occurrence to its raw branch list and then flattens those lists. It retains duplicates and empty rejecting branches. It derives successful concrete actions from the existing producer; it does not accept an action-success or output law as a premise.

The selected-list membership premise ties every selected edge to the same actual ordinary parent. It does not establish canonical or weighted order. A missing model projection remains outer `none`; it is not a native Haskell error or reject. Successful unsupported traversal remains the inner `none` with its actual prefix endpoint. The native incoming-terminal dispatch, full eager/raw driver, terminal child merge, native heap/Graph correspondence, machine IDs, solver and full-language obligations remain outside this component. This clearance adds no end-to-end claim. The full goal remains ACTIVE and H6 remains the strongest result.

## Checked identities

All hashes below are SHA-256.

| Input | Bytes | Hash |
|---|---:|---|
| V2 pins.json | 17039 | `3c0bb2dd51b25855a698ecd76132cc9c632584106f4995ab38ecbbd02af727e7` |
| V2 FROZEN.json | 3623 | `1fd433fecbfa94330c6e7fced1f4370e2b7ad3719c98fab33d01d9784643cc5f` |
| V2 contracts.json | 3785 | `cadf2a32792c4b24a4f1f7bfe2ac28207a062e00e815f6e3db91067db0f5d734` |
| V2 local-cons-raw.lean.txt | 375 | `efd02c3afa4dee95edb30a048bb1492816acfbd0d1de7b42f660d1b35b6e6e61` |
| V2 induction.json | 3723 | `f5a0ba3682729059572421cabe9bba822420dde199d361c675986252e5c1f2d5` |
| V2 v1-v2-delta.json | 2353 | `6aca9a7630ffd95c2b3471e1f461d3f8edc7a240f4137987855d707938a5d240` |
| Except.lean full snapshot | 11467 | `d388b93b3a59dc804743a0cfa7394f64653f5a15d54e584736aa61e1660c7e4c` |
| Except.lean lines 128–149 | 779 | `10269ab0ab0e6bad76ff0c429e46b079845dc3243ce3e76c78a84259bbc072de` |
| Actual strict-1 failed input | 5911 | `e04a6696d37614bee3ded56b1cda19045c24729261e475cd00a6f4d4c485ed91` |
| Actual strict-1 raw.log | 20184 | `6fc6d6e38fc64fa2c12a1f4f68d6eb8b31a9bd89040ef43699cd23f7ba170930` |
| Actual strict-1 report.json | 663 | `fdf8892da06273ac93d5556a1331074f848153c60c55e732cfb85a2d1b9cd008` |
| V1 body-gate.json | 6004 | `0cb7a06233641d602cd674a6b8cdd3f93ac13b393330c3db7f41df401138dff6` |
| Immutable V1 declaration review | 11777 | `8ac6f7eb8b62a3a3d0ba0959d19d83aa3a595151d263e3d69e95ea8ee685fd4e` |

Owner: `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal-v2`. Original owner: `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal`. No owner, prior report or repository file was modified during this review.

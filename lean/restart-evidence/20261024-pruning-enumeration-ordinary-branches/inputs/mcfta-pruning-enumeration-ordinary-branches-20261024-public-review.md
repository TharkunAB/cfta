# OrdinaryBranches public signature and axiom review

Reviewed at 2026-10-24T17:34:39+02:00. Verdict: CLEAR. I read the complete 52-line, 3,520-byte actual public output, both full compiled signatures, both actual axiom reports, the seven-line public input, its successful report, the V2 gate and the complete installed 110-line source. This is an independent static readback review. I did not author the definition or theorem body, run any compiler or selected program, or modify the repository. I authored the prior source and declaration reviews; those reports remain unchanged.

## Compiled public contract

`MicroCFTA.SourcePruningEnumerationOrdinaryBranches.run` has the exact approved input list of suspended constraints and selected concrete edge values. It returns the existing `EnumerateM` over full `SourcePruningTemplates.Symbol` and `SourceSymbolicIndex.Constraint FullSyntax.Formula`, with result `Option (Option Fragment)`. The output retains both Option layers. The compiled signature has no added heap, callback, success premise, equality instance or carrier parameter. The definition remains noncomputable.

`run_complete` has the exact approved parameter order and domain: the same suspended constraints, heap, actual ordinary parent entry and stored rows, selected rows, depth and free references; `Ready heap`; availability of that same full parent; `free = []`; selected-edge membership in those stored rows; and the actual enumeration `before` with `PendingRealized heap before` and counter/list alignment. It has no assumed branch-success, projection-success or output-law premise.

Its compiled result preserves an ordered `Language.All₂` relation between the selected rows and raw branch lists. The actual Bool coercion prints as `arityAllows ... = true`, as expected. For false arity the raw branch is empty. For true arity and missing model projection the raw branch is exactly `[ok (none, before)]`. For a present projection the conclusion derives the actual prepare action, observed result and full final state, their `Success`, exact singleton `[ok (some result, after)]`, final alignment and final `PendingRealized`. The final equality is the complete `run ... before = branchRows.flatten`. The printed existential names and omitted inferred binder annotations do not change the frozen statement.

I read every line of the actual output. There are two full `#check @...` signatures and two axiom reports. There is no ellipsis, deep-term omission, `sorryAx` or extra project axiom in that output. The public input changes display options only: `pp.deepTerms true` and `pp.maxSteps 1000000`. These do not change theorem assumptions or proof limits.

## Actual axiom sets

Both declarations report exactly the same three axioms:

| Declaration | Actual axiom set |
|---|---|
| `run` | `propext`, `Classical.choice`, `Quot.sound` |
| `run_complete` | `propext`, `Classical.choice`, `Quot.sound` |

The definition is not axiom-free. The actual definition report includes `Classical.choice`. I compared the raw reports to `public-declarations.json`; the sets agree exactly. No empty axiom set or stronger constructive claim is inferred.

## Gate, literal correspondence and actual checks

The accepted V2 gate was recorded at 2026-10-24T17:30:51.240502+02:00. It binds the exact V2 pins, FROZEN, ten contract strings and final declaration-review hash. Its copied contracts equal the frozen owner contracts. I checked all 121 owner payload pins and the complete 123-file set. Only top-level pins/FROZEN are excluded; historical failures and nested controls remain pinned.

Each of the ten frozen declaration fragments occurs literally once in the installed source. The two public header attachments are exact: plain ` :=\n` for `run` and ` := by\n` for `run_complete`. The one approved local List Monad uses singleton `pure` and ordered `flatMap` bind. There is no additional instance, helper, type, predicate, public declaration or adjusted limit in the source. Four haves, three obtains, the single fixed-before list IH and its proper-tail call remain within the approved inventory. The five-line raw-list declaration contains the explicit `ExceptT.run` projections from V2.

The installed 6,368-byte, 110-line source is byte-identical to the actual strict-3 input. Strict-3 exited zero with a literal empty raw log under warning-as-error and all linters, with default proof limits. The strict-1 and strict-2 reports both record exit one and remain retained. The actual final proof changes expose the raw bind equations and normalize the same matched action before `bind_single`; they do not change the definition, public statements or V2 local type. This review does not call the development a first-attempt pass.

The actual public-1 report records exit zero and binds the exact 3,520-byte output. The installed-1 report records exit zero. I read its complete short raw log: it completed 624 jobs and replayed the older unused-variable warning in `InternedFreshOrdinaryClosedCompletion`. That warning is not a new warning in this module. I did not run or repeat any check. Audit, seal, commit and push results are outside this review and are not inferred.

## Scope retained

The source selects a concrete edge before it prepares that branch. Alternatives start from the same `before`; they are not a sequential fold of branch endpoint states. Ordered raw lists retain selected occurrence multiplicity and empty rejecting alternatives. The theorem's membership premise does not certify a canonical or weighted order. Outer projection absence is a model-domain case, not fabricated native Haskell rejection or error. Inner unsupported traversal retains its actual endpoint. The native incoming-terminal dispatcher, terminal child merge, native heap/Graph bridge, machine identifiers, solver and complete public driver/language claims remain open. H6 remains strongest and the full goal remains ACTIVE.

## Exact evidence identities

All hashes are SHA-256. Paths below `work/` resolve under `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/`.

| Input | Bytes | Hash |
|---|---:|---|
| Installed source and strict-3 input | 6368 | `c46228a592055ff1c5cc844106676a953e7a238017308a82979254ddf2e8a558` |
| work/public-1/raw.log | 3520 | `141c3bd0e71239e35584f209171796b722247b73c495379f33a8ef9d3ed464d8` |
| work/public-1/checked.lean | 400 | `65c5d9ee870c3abc43d0805a61c50dbbd7c295e2987a952702297a041c9a5202` |
| work/public-1/report.json | 531 | `8bdf3f9fbe806cc3054ed89aab9f94e20b3676dbd625bff663755d9bb67181c3` |
| work/public-declarations.json | 783 | `c60a5500efa74a672ec1c1a8ef708fe16f56c226b0f8820653438c0f07d0fd8e` |
| work/body-gate-v2.json | 5388 | `e648f6e441ecb9187b081d2bf86438078a04d376316b378b7fdd17c723b30af7` |
| V2 pins.json | 17039 | `3c0bb2dd51b25855a698ecd76132cc9c632584106f4995ab38ecbbd02af727e7` |
| V2 FROZEN.json | 3623 | `1fd433fecbfa94330c6e7fced1f4370e2b7ad3719c98fab33d01d9784643cc5f` |
| V2 contracts.json | 3785 | `cadf2a32792c4b24a4f1f7bfe2ac28207a062e00e815f6e3db91067db0f5d734` |
| Immutable V2 declaration review | 8207 | `775025cb491ee8835b1fe65fd8efc889d948f788e0612d6ca00001b4b29945bf` |
| work/strict-3/report.json | 659 | `970a11afa03fd1b88f500de1bd4844ef59f2f2ab336b66ad12a70434830cb794` |
| work/strict-3/raw.log | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| work/strict-2-to-3.patch | 1171 | `ade52773c225195ebc6d157ce5d95ce8e38f24fab0e53ef5b02b9df5bd4b6ad7` |
| work/installed-1/report.json | 335 | `bfa49075728a40a501df31dc17c49d33ca50460979d753e23e2c4179f9a85293` |
| work/installed-1/raw.log | 558 | `4598238e088a4c0eca34b5263a262d2864b8aaa4c6dc1496d6ef5f7e12ed01bc` |

Installed source: `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationOrdinaryBranches.lean`. Frozen owner: `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal-v2`. Earlier reports and owners remain unchanged.

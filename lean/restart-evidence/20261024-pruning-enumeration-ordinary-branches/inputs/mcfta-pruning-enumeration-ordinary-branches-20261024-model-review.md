# OrdinaryBranches final source/model review

Recorded: 2026-10-24T17:34:22+02:00. Verdict: **SOURCE_MODEL_CLEAR** for the exact final source below. This is a static source/data review. Arity authored the declaration owners and this review. Root authored every production definition, proof and local instance body, and ran all compiler jobs. Guard independently reviewed the original and revised declarations. The declaration-author role is disclosed; this is not an independent review of Arity's own declaration authorship.

I read all **110 lines / 6368 bytes** of the final authored module, both complete failed raw logs and reports, the retained two patches, V1/V2 gate and literal contracts, the frozen scoped IH/case/obtain plan, and the concrete imported completion/uniqueness/raw-bind APIs. Final source equals the strict-3 input byte for byte. All ten V2 literal fragments occur exactly once. All 121 V2 payload pins match their bytes and SHA-256. V1 remains historical and unchanged.

## Actual behavior and proof

- `run` has one `choose selectedEdges` followed by the SAME selected edge's `EdgeTraversal.prepare`. There is no preflight, filtering, sorting, deduplication, recapture or sequential state fold across alternatives. Each alternative starts at the SAME `before`. The local `ordinaryMonadList` implements singleton `pure` and ordered `flatMap` bind, as required by the imported concrete enumeration laws. It is module-local, with no LawfulMonad or global equality instance.
- The three relevant outcomes remain separate. False inherited arity gives raw `[]` before projection. A missing projected constraint gives one `.ok (none,before)` marker for the model's unsupported projection domain. A present edge action wraps its existing result in `some`; actual child-unsupported `none` therefore becomes `some none` with the actual reached prefix endpoint. Complete fragments become `some (some fragment)`. These markers are not claimed to be native Haskell outcomes.
- `run_complete` derives per-occurrence raw rows from genuine `Ready`, actual ordinary-parent `Available`, closed parent, concrete selected-edge membership, actual pending realization and supply alignment. It does not assume a callback singleton law, desired action success, Graph equality, child result, output heap or row order. Arbitrary selected-list order and repeated equal edges are allowed. The theorem retains each occurrence and flattens its exact raw row in that order; repeated output entries remain repeated.
- The sole structural induction is on `selectedEdges`. The dependent membership premise is generalized automatically; `before` and the other environment arguments remain fixed. `ih selectedTail` is the only IH call. The nil case produces the empty stream. In the cons case, `selectedHead` and `selectedTail` come from the actual supplied membership proof.
- The revised `consRaw` projects all three `ExceptT` values with `ExceptT.run` before List append. Its proof unfolds only the concrete chooser/bind representation. This preserves the tail at `before`, rather than accidentally continuing it at the head endpoint.
- There are exactly four typed local haves: `selectedHead`, `selectedTail`, `consRaw`, `actionRaw`. There are three obtains, with 3 + 2 + 13 fields, including all explicitly skipped completion fields. There is one Bool condition, one projected Option case family, no proof `let`, no extra helper, no extra action, no recursive declaration, and no new type/predicate. The one action is the declared `run`.
- In the enabled/projected branch, the proof calls `EdgeTraversal.prepare_complete` once at the SAME parent, selected head and `before`. It retains that packet's action, actual observed mapped fragment/result, actual full `after`, alignment and all-slot realization. `RawExact.prepare_exact` then turns that SAME observed success into its entire raw singleton. `bind_single` wraps that singleton; no unrelated witness or stronger assumed output law replaces it. The child-middle/residual fields are consumed as existing packet fields, not re-proved or advertised as an expanded public packet.
- The concrete raw singleton excludes additional errors/results for that supported per-edge action, using the existing source-specific uniqueness theorem. It is not a general assertion that arbitrary enumeration actions cannot fail. The raw definition still carries errors through the existing ExceptT bind. Raw duplicate elimination is not performed; only extra alternatives within the SAME completed edge action are excluded.

## Actual failed attempts and correction lineage

`strict-1` genuinely failed. Its first errors were unnecessary explicit `generalizing selected` and a missing HAppend instance because V1 `consRaw` appended ExceptT containers. The downstream witness/elimination goals remained in that invalid local type context. V1's source, full 20184-byte log, report, gate, owner and prior review remain retained. The new V2 owner changes the local raw-list projection and exact induction command metadata; its public headers, context and every other local literal remain unchanged. The fresh body-gate-v2 precedes the revised Root body.

`strict-2` also genuinely failed. The revised statement was retained, but a one-shot `simp only` did not expose the chooser's concrete raw cons decomposition, and `bind_single` did not match the unreduced `match some action`/ExceptT view. Four unused-simp diagnostics were also present. Root's retained strict-2-to-3 patch changes only these two proof sites: explicit `unfold run; rw [run_bind, run_bind]` before the concrete list reduction, and an explicit raw `change` before `bind_single`. No public/local type, definition, helper, instance, hypothesis or resource option changes in this second patch.

`strict-3` reports exit 0 and a literal empty raw log, with warnings-as-errors and all linters in its recorded command. The final authored source is exactly that successful input. This review did not run the compiler, import a candidate, execute prepared scripts, alter the repository, or repeat a check. It does not assert any later installed-build, Audit, public-output, seal or push result.

## Scope boundaries

This is a source-specific shallow edge branch body over a concrete selected edge list, with a proved exact ordered raw producer. Native `enumerateShallowHere` calls such a body only for terminal-free incoming constraints. Public `runsInterned` uses raw stored edge order with eager `enumerateNode`; public shallow `termsPruneUntil` initializes canonical order. This component is not equality with either complete public entry. Actual canonical/weighted ordering, terminal intersection/assimilation/emptiness, native cache/NodeId realization, outer driver coupling, typing, complete language preservation and convergence remain separate. Inherited noncomputability comes from the existing projected accessor. The strongest H6 statement is unchanged, and the whole goal remains ACTIVE_INCOMPLETE.

## Bound identities

| Object | Bytes | SHA-256 |
| --- | ---: | --- |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/authored/MicroCFTA/SourcePruningEnumerationOrdinaryBranches.lean` | 6368 | `c46228a592055ff1c5cc844106676a953e7a238017308a82979254ddf2e8a558` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal-v2/pins.json` | 17039 | `3c0bb2dd51b25855a698ecd76132cc9c632584106f4995ab38ecbbd02af727e7` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal-v2/FROZEN.json` | 3623 | `1fd433fecbfa94330c6e7fced1f4370e2b7ad3719c98fab33d01d9784643cc5f` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal-v2/contracts.json` | 3785 | `cadf2a32792c4b24a4f1f7bfe2ac28207a062e00e815f6e3db91067db0f5d734` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/body-gate.json` | 6004 | `0cb7a06233641d602cd674a6b8cdd3f93ac13b393330c3db7f41df401138dff6` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/body-gate-v2.json` | 5388 | `e648f6e441ecb9187b081d2bf86438078a04d376316b378b7fdd17c723b30af7` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-declaration-review.md` | 11777 | `8ac6f7eb8b62a3a3d0ba0959d19d83aa3a595151d263e3d69e95ea8ee685fd4e` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-declaration-review-v2.md` | 8207 | `775025cb491ee8835b1fe65fd8efc889d948f788e0612d6ca00001b4b29945bf` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-1-to-2.patch` | 2772 | `76812a8d01b70e42e9472dc1755de099aa10baae8178feca4c6d05c72642b673` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-2-to-3.patch` | 1171 | `ade52773c225195ebc6d157ce5d95ce8e38f24fab0e53ef5b02b9df5bd4b6ad7` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-1/report.json` | 663 | `fdf8892da06273ac93d5556a1331074f848153c60c55e732cfb85a2d1b9cd008` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-1/raw.log` | 20184 | `6fc6d6e38fc64fa2c12a1f4f68d6eb8b31a9bd89040ef43699cd23f7ba170930` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-1/MicroCFTA/SourcePruningEnumerationOrdinaryBranches.lean` | 5911 | `e04a6696d37614bee3ded56b1cda19045c24729261e475cd00a6f4d4c485ed91` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-2/report.json` | 663 | `99e5854d4a7745a1c92c313bd2f65ab80dfd4efc10076e719e26f0b628828066` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-2/raw.log` | 15227 | `f47b49825973ffd246ffd74bc788600bd30da951781c6ee853a186f8de832aa0` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-2/MicroCFTA/SourcePruningEnumerationOrdinaryBranches.lean` | 6199 | `47543aa9671b931d18fef4511b532ed2a0850d88bb8ef40dedb5b40665cf5cc8` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-3/report.json` | 659 | `970a11afa03fd1b88f500de1bd4844ef59f2f2ab336b66ad12a70434830cb794` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-3/raw.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024/strict-3/MicroCFTA/SourcePruningEnumerationOrdinaryBranches.lean` | 6368 | `c46228a592055ff1c5cc844106676a953e7a238017308a82979254ddf2e8a558` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationRawExact.lean` | 8945 | `687a5e58c4403076a22e249a981c3a733bc3d5d4f5c32acd4f15af70022c07ae` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean` | 15377 | `9a071434740188ae3b03c06b6ed0487d1d3856aaaac0a8b0d7ff4bca4c1271bc` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationEdgePrefix.lean` | 5270 | `fd80b9c8ff6d9f3656837186a18f584e2a077b0b703489b9077a9f56e5bc56d1` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCorrectness.lean` | 76898 | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` |

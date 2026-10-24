# Prospective ordered edge-child traversal

Review cut: 2026-10-24 10:52:36 CEST. SOURCE ASSESSMENT ONLY. This report stays outside the active archive glob. It selects no header, body or compiler action.

**Next substantive operation:** run the SAME returned prefix action once, traverse its captured child Options left-to-right, build the actual symbol/child-fragment node, then record its residual ONLY after child-list completion. Use existing OptionT over EnumerateM; no new state/error carrier, callback interface or Graph law is needed for this partial operation. Preserve prepare’s OUTER Option for checked projection absence. The inner Option marks unsupported traversal, not that outer absence or a native result. Retain fixed full Symbol and complete Constraint FullSyntax.Formula.

The actual prefix action supplies the symbol, stages, residual and suspendedState endpoint. Traverse that captured list, not a separately recomputed preparation. A present child action runs at the current state; a missing action stops with None at that ACTUAL state. OptionT bind does not roll back earlier allocations. Rejection stays no list results, and existing Except errors stay errors. Unsupported is ok None with the actual prefix state; it is not a new enum error, native pending result, final fragment or proved resumable source continuation.

Do not preflight the entire list for missing Options. In a raw staged list with an earlier reject and later missing action, the earlier reject must win. A preflight would incorrectly return unsupported success. Earlier errors must also win, and earlier child allocations must remain before later unsupported entries. These are source/effect-order examples, not executed native reproducers or bug claims. Genuine live-edge facts may exclude some raw examples, but a general traversal must not assume that exclusion silently.

On successful list completion, construct the node from the captured symbol and returned fragments in original child order. Use existing `EnumerationSchedule.recordResidual` at lines 1196–1200: None leaves state unchanged; Some prepends the COMPLETE constraint with this ACTUAL fragment. Do not record a parent residual on unsupported/rejected/errored traversal. This is the source order in Enumeration.hs:766–774.

## Certificate and existing APIs

Tie the result to the actual prefix packet, rather than arbitrary supplied actions or a callback-output law. Reuse prepare_complete for the actual equality-allocation endpoint. Use prepareChild_complete on each same native child and COMPUTED bucket, and pass its actual returned after-state to the next child. Retain full ancestry/values/forest effects, alignment and PendingRealized at those SAME states. Do not reconstruct a counter-only state or use full Frame across allocations/writes.

A producer for completion needs genuine nonempty available closed children and nonterminal COMPUTED buckets, obtained from the same parent/exposure records. These differ from desired-success premises: existing child producers derive actual actions, payload readbacks and states. Each supported nonempty child allocates one slot; ordinary children write the full bucket, while Mu/retained-union children retain the documented empty-suspended truncation slot. Empty runs reject first. On arbitrary data, absent child Options can also arise from unresolved references or encoding absence; do not call every None terminal. Real closed availability lets existing readback facts exclude those cases.

Current supported child actions leave native heap fixed, so native record facts remain at that same heap. Recording the parent residual changes obligations but not pending value slots; derive realization through unchanged values rather than claim full Frame. Existing success_bind, success_pure, modify_success and mapM_sound support sequential certificates. mapM_sound preserves invariants under SUCCESS; it does not itself derive child success. At most one small ordered-list helper is reasonable. If a mapM proof needs LawfulMonad for the named local List Monad, inventory and reuse the existing exact law pattern.

## Remaining substantive connections

Terminal merging is STILL OPEN. Its actual source path reads representatives, unions variables/transfers waiting counts, assimilates values and intersects native nodes. OptionT exposes the missing path; it does not implement it. Substituting an old Graph-driven eager action requires a genuine native Value/handle/Graph/intersection bridge, not a desired Graph output law. Terminal intersection can change the actual native heap and later child readbacks. The current fixed-heap worker cannot be assumed to cover it.

Own arity already has a native guard: mkEdge checks contradiction and fitsArity (`Interned/Type.hs:554–568`), and setChildren preserves equal arity or rechecks (`389–401`). Existing SourceEqualityMkEdgeAllocation.accepted/build_receipt and SourceEqualityMkEdgeArity.fits_exact model these checks. No new native fix or run-time own-arity rejection is needed.

The future receipt integration must identify the SAME actual live returned edge’s symbol, complete constraint and ordered children, follow the accepted branch of that constructor run, then transfer fits_exact bounds through project’s trie readback. Existing field/child certificates, including SourceEqualityRequiredCache.edge’s exact children, provide part of this route. Do not use the original requested constraint’s successful arity law for a rejected empty-edge sentinel. This receipt-to-edge-to-trie transport remains separate from operational traversal.

**Fresh estimate:** target 150–220 ordinary lines, proposed hard 260, for concrete staged traversal/composition and actual-state supported/unsupported certificates, with at most one ordered-list helper. Excludes terminal merging, native Graph/heap adaptation, constructor receipt transport, selector correctness and whole-driver language proofs. If included, revise scope before exact declarations. No body authority is granted here.

Default canonical/weighted selection differs from stored edge-ID order; this operation consumes one supplied actual edge. Physical Nat IDs are the model convention, not native extraction. Recursive truncation does not prove nonempty language below a marker. Projection/prefix remain noncomputable source models. Native Int/container bounds, solver soundness, global termination and whole-driver correctness remain open. H6 is unchanged; the full goal remains ACTIVE.

I authored no declaration, body or candidate. I ran no compiler, parser, selected/prepared program, import, probe, Git, network or board action, and changed no repository/current checkpoint/old report. Only this prospective report was written.

## Input identities

Whole-file hashes identify inputs. Locations are bounded excerpts; earlier complete body reviews were reused at exact identities.

| Input | Locations | Bytes | SHA-256 |
|---|---|---:|---|
| `/tmp/mcfta-pruning-enumeration-edge-prefix-20261024/SourcePruningEnumerationEdgePrefix.lean` | complete 94-line source review | 5270 | `fd80b9c8ff6d9f3656837186a18f584e2a077b0b703489b9077a9f56e5bc56d1` |
| `lean/MicroCFTA/SourcePruningEnumerationShallowChild.lean` | 14–62; prior complete body review | 6479 | `8210b17170fce05b31515e5f9b332799601fcfbc728263df6e2f53b917baed7c` |
| `lean/MicroCFTA/EnumerationSchedule.lean` | 1195–1201 | 86287 | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 56–64,1008–1011,1071–1090 | 76898 | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` |
| `lean/MicroCFTA/EnumerationDriver.lean` | 195–204 | 52410 | `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf` |
| `lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | 19–27,45–55 | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` |
| `cfta/src/Data/CFTA/Enumeration.hs` | 756–801; previously read canonical-order cuts | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` |
| `cfta/src/Data/CFTA/Interned/Type.hs` | 389–401,554–568 | 36883 | `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77` |
| `lean/MicroCFTA/SourceEqualityMkEdgeAllocation.lean` | 17–39,117–143 | 9641 | `5365ae3e5a39760b9052aef795c9eb609fb726516960fc48f5ef55367e41236a` |
| `lean/MicroCFTA/SourceEqualityMkEdgeArity.lean` | 27–44 | 9191 | `85be9feb608565f4d666bcb7ea2af5576eac1ba5544818f8d7e6b06ab2faf816` |
| `lean/MicroCFTA/SourceEqualityRequiredCache.lean` | 49–65; previous field-certificate review | 6081 | `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733` |
| `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Control/Option.lean` | 24–63,80–96 | 3755 | `8561d3ad9e9bd0bf4b5c4712c5490c3a0821cabd64e7f4006f7a8ef74824f151` |

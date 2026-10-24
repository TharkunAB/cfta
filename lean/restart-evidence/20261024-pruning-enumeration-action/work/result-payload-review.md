# Narrowed result payload clarification review

Status: SOURCE_ONLY_PAYLOAD_HOLD_RESOLVED. Reviewed 2026-10-24 at 08:21 CEST.

Arity authored the prospective assessment and this addendum. I independently reviewed their payload contract and the exact source correspondence. The original assessment and its HOLD report remain unchanged. This clearance concerns prospective declaration selection only. It authorizes no declaration, action, proof body, compiler job or change to the sealed checkpoint.

I read all seventeen addendum lines, its complete input-identity metadata and all nine exact source cuts. The additive contract resolves the original omission: retain the actual narrowed Value outside Option of the existing EnumerateM Unit action. Use existing product output data inside the existing output-polymorphic Result; keep the actual native heap in Result. This requires no product state, new carrier or mandatory returned-handle field.

Enumeration.hs951–959 gives the generic callback a Node. Lines981–992 pass the same actual narrowed node to Right after the conditional slot action. An action-only payload cannot preserve that input. Retaining Value explicitly supplies it without rerunning narrow or assuming a desired-action/output equality. The template callback happens to ignore Right at Pruning.hs238–240 and SourcePruningOracle.lean56–68. That specialization does not weaken the generic driver contract.

The branch distinctions are correct. Empty selects the actual rejection action before encoding or handle equality. Its empty list prevents the Right continuation. A completed nonempty unencodable result retains its Value and native heap with None. An encoded nonempty result retains Value with a pure Unit action on equal handles or the existing representative-bind-write action on changed handles. The action may capture the computed handle; the later native continuation needs the retained Value. Native failed preserves its actual fault/heap, while an enumeration error remains an error of the returned action. Neither is the None marker. The chosen Ready/available/closed completion can exclude encoding absence by its derived readback; arbitrary executable inputs do not acquire those premises.

MergedSourceComparison.lean22–36 supplies exactly the required generic success/failure carrier and heap-preserving bind. EnumerationState.lean85–96 distinguishes rejection from enumeration error. Its Oracle at296–298 takes Nat rather than native Value. Therefore this addendum does not establish direct reuse of the old pure-Nat Oracle. Native Value/Graph classification, raw NodeId extraction, cached-state realization, the full driver and typedTypes composition remain open. Any later right-action composition must preserve the actual E/Q/F and H′ already obtained; this review proves no such action theorem.

Static checks verified the exact four-file addendum set, with only its own top-level pins.json and FROZEN.json excluded from its two-payload map. All byte lengths and SHA-256 values match. The four original control identities and all fifty-six original payloads remain unchanged. All six live defining source identities and all nine line-cut byte identities match the addendum metadata. Full sources were hashed programmatically; this review manually read the selected cuts, not every imported source.

Original immutable HOLD report: /tmp/mcfta-pruning-enumeration-outer-20261024-next-source-review.md, 7492 bytes, SHA-256 634266334414ac07749feb378290b957bfdd538d055bc1504a06af614d4743cd.

Addendum owner: /tmp/mcfta-pruning-enumeration-outer-20261024-result-payload-addendum/.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| addendum.md | 2739 | ff19ace1f78be3b8dc6f51b60a6cd1b4206d936bccba0d52899ba08ef46a2052 |
| input-identities.json | 3827 | 9348fe3df064293df2bd2f561a0294b9bd63638f7b4f8e01084fc9e0845448aa |
| pins.json | 261 | 1a2c44a811975f5bcf772f1326c7f3959e002958f18adb74d7e21bf70770b71d |
| FROZEN.json | 463 | 7e282369790c31cecc24978664e5befa690d847aa3f786c52c79d2eff9cb5b93 |

No selected-program execution/import, compiler, Git, network, board, repository mutation or modification of either frozen owner occurred.

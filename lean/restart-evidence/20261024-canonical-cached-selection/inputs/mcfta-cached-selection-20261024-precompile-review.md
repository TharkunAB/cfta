# Canonical waiting, compression frame, and pure selection: source review

Reviewed at 2026-10-24 01:35 CEST. **SOURCE CLEAR for all three current candidates.** I read every line and found no definite type, proof, or statement-scope error. This is precompile source clearance, not a claim that the three-file candidate has compiled. No Lean/compiler command, prepared program, or repository mutation was run by this reviewer.

| Candidate | Lines | SHA256 |
| --- | ---: | --- |
| `/tmp/mcfta-cached-selection-20261024-canonical-waiting.lean` | 239 | `fcb7c910fb67bf253bfb7c6b5ed9d1bb1f5e186cb78cf18f52e7a9cbe7dbdd70` |
| `/tmp/mcfta-cached-selection-20261024-compression-frame.lean` | 145 | `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` |
| `/tmp/mcfta-cached-selection-20261024-selector.lean` | 190 | `c5c57b1a8c3afe7f3dfe8ad8d7ad79d6deaaac833d0fc82bf4ff12c50ecb82b5` |

Guard authored canonical waiting. Arity authored the frame, with Root's stated explicit-substitution correction and field documentation. Root authored the selector. I authored none of these bodies. The already reviewed pure-root candidate remains separate at SHA256 `83e4cca222e43535bd10b33ef11c4a323132cbe399fd59dee76180ff27ef219f`. Root reports that worker and the corrected frame passed their checks; I did not rerun them.

## Canonical waiting

`canonicalValue` changes only suspended reference IDs in a count view. It leaves node IDs, tries, stored fragments, and eliminated tags unchanged. Its use does not claim that the renamed value list is an executed machine state or a semantically interchangeable constraint store. `Correct` is exactly the old raw-count equation applied to this view. The references and candidate lemmas have the correct orientation. Candidate preservation follows because reference renaming preserves whether the suspended list is empty.

Replacement removes old references before adding new references under a fixed supplied map. The proof uses the actual `List.map_set` equation and existing waiting replacement theorem. Allocation appends a slot with no references. Support is precisely the existence of an original suspended reference whose supplied image names the key. The map membership substitutions retain the original trie and occurrence.

`move` matches the native sparse counter move for a distinct source and target: missing source leaves the table alone; present source is deleted and its amount is added at the target with default zero. It deliberately uses `some (sum)`, as native `insertWith (+)` does, rather than silently encoding away zero. The proof supplies the missing reason this is safe: Correct gives a strictly positive source amount and a nonnegative target count, so the new sum is nonzero. The absent-source branch derives that the source count is zero. The same-source branch is an identity. No source/target fixed-point assumption is used to invent positivity or canonicality.

The occurrence/total redirect equations account for source deletion, target addition, and every unaffected key. `moveMany_correct` threads the same ordered fold through the waiting table and a ghost reference-map redirection. Duplicate source names and inclusion of the target are handled by the literal move definition. This is a count-update theorem. It does not assert that the ghost map is the actual forest root map between native bulk-union operations, or that candidate/live-slot invariants hold at those intermediate operations. Connecting the completed native union to the final ghost map remains a separate source-lift obligation.

## Complete compression frame

The frame preserves counter, full value list, obligations, the entire per-variable recursion ancestry function, and expansion ancestry. Its forest relation is equivalence of each finite root path with both representative ID and stored size. It therefore addresses the omissions in RenderStable without assuming that arbitrary callbacks respect compression.

Reflexivity and composition orient all field equalities and path equivalences correctly. `Frame.total` transfers each actual finite root path. The pure/get proofs use the actual success equations and explicit state substitution. Representative and value reads use the live successful-find equations. Total is required only where `findRoot_reaches_iff` needs the reverse implication. `getValue_frame` also returns the same actual representative, size, and original stored slot.

The suspended-reference and complete-scan folds use `Frame before` as the invariant. Each previous frame supplies Total for its actual next state. The final pure result/finish step has the correct unchanged-state equation. No counter, ancestry, or residual field is lost between the local read lemma and the complete scan. The code makes no equal-fuel claim across different forests.

## Pure selector and public theorem scope

`EnumerationPureSelection.Correct` records index equations **at the supplied map**. It does not itself assert `Roots` for that map. Thus `frame_correct` is correctly a fixed-map index equation, and `transfer_correct` follows a ghost map while leaving the core forest unchanged. Neither statement establishes an actual native intermediate union invariant. This separation is essential and is respected by the main bridge premises.

Initial, allocation, and write facts use the actual same slot/counter effects and canonical count equations. Candidate-list equality preserves the ascending slot order and relates it to the stop test's complete pending list. `find` tests the candidate list before subtracting canonical waiting support. It keeps Nothing distinct from Some empty. It does not resolve any representative or alter any state. `next` reuses the existing preference-membership/fallback function.

`findAction` uses the existing source CPS state primitive on `(Cached Symbol Guard)`. `findAction_represents` instantiates the exact live `EnumerationCPS.state_represents` theorem with `(find state, state)`. The returned state is the same **complete Cached value**, including both indexes and all core fields. It is not merely a projection or a core-state equality.

`find_exact` connects canonical support to `scan_blocked`, equates the candidate folds, and checks both Option cases when proving filter equality. The support equivalence has the correct direction in both branches. No positivity assumption is lost: it is already derived from Correct by the canonical support theorem.

`scan_agrees` adds `Roots state.core.representatives roots`. From those actual finite paths it derives Total; it does not demand an extra independent Total premise. The equality composes the existing successful old-scan summary with `find_exact`. The frame comes from the actual old scan and its exact input/output states. `scan_complete` obtains a finite old scan from the existing termination theorem and substitutes its result using the equality from `scan_agrees`. It preserves that same output state's frame. It does not assert successful old scanning at every bound, exact final-forest equality, callback congruence, or whole-driver equivalence.

## Live helper checks and remaining gates

I checked the actual signatures of waiting support/positivity/replacement/allocation, candidate and blocked fold lemmas, `foldlM_invariant`, get/representative success equations, `findRoot_reaches_iff`, `findExpandable_exact`, scan termination, and CPS state representation. Relevant live identities are:

| Source | SHA256 |
| --- | --- |
| `lean/MicroCFTA/EnumerationWaitingIndex.lean` | `3dd9d39df6a289d3b9689280f0dbb786ea4609b8132016d1e4178d2ea9c0d8e5` |
| `lean/MicroCFTA/EnumerationIndexSelection.lean` | `ae067c7531435870f7c4fb84f13c93feced5c8f81cdd11fc621939fd77e9fcdc` |
| `lean/MicroCFTA/EnumerationDriver.lean` | `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf` |
| `lean/MicroCFTA/EnumerationExecution.lean` | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` |
| `lean/MicroCFTA/EnumerationCPS.lean` | `51ec329d9ed0fc9a7cbf432670602e5904f3d6b2802d54f36d40ccf275d5646c` |
| `lean/MicroCFTA/UnionFind.lean` | `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14` |

The candidates retain the intended source boundaries: finite dense views represent the cached sets; the count map is ghost-indexed until related to actual roots; and no native bulk-union intermediate preservation or arbitrary observer law is claimed. Root's combined compile, installed build/Audit, and complete checked public-type readback remain separate acceptance gates. H6 and the full-system gaps are unchanged.

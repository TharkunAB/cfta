# Independent resume source review

Review time: 2026-10-24T02:54:56+02:00. Status: SOURCE_ONLY_REVIEW_CLEAR. I read all 242 selected source lines and the entire author self-review. I checked the live Haskell `resume`, the imported matcher identity, and the actual observer/frame/fuel APIs below. I did not author this resume source. I did not compile, import or execute selected code, edit the repository, mutate Git, use the network or post to the board.

The selected source is 15277 bytes, SHA256 `593d1b84050ba85d130f32a57947be90374b29f66ca9a649a1070855757d024d`. The self-review accurately describes the implementation and proof scope. No semantic or proof-contract correction is requested. Compilation and strict-linter acceptance remain Root's checks; this receipt does not claim them.

## Literal source behavior

`part` first runs the existing effectful representative lookup for the parked ID. It compares the returned root with the unchanged raw `current`. On equality it calls the exact imported pure `matchPartial`; otherwise it retains the exact pattern with the returned root. The result is an `Option Pending` VALUE inside `EnumerateM`, not an action rejection. A pure mismatch `none` therefore does not bypass the next representative lookup.

`resume` executes the complete ordered `pending.mapM part` before its pure `Option` traversal and concatenation. This matches Haskell's `fmap (fmap concat . sequence) (traverse part pending)`. A list containing an early `none` still performs all later representative reads on a successful stateful traversal. A representative lookup that fails at the chosen bound can still prevent action success; the theorem makes no false claim that pure mismatch overrides such a failure. The empty pending list succeeds without a read, including at fuel zero.

The pure combination preserves list order, every pattern, every encoded raw ID and every duplicate. It returns `none` when any pure part returns `none`; otherwise it concatenates the successful pending lists left to right. Neither definition normalizes `current`, sorts or deduplicates pending entries, assumes canonical current, substitutes an arbitrary matcher callback, or replaces the actual representative action with a pure root oracle.

## Proof and state audit

- `part_success` exposes the actual representative transition with the SAME final state as the pure part result. Its pure-result equality direction agrees with the existing `success_pure` API. `part_frame` uses `representative_frame` with Total at the actual input state. `part_agrees` and `part_transport` apply the installed primitive observer theorems to the same parked ID, then use the deterministic matcher result.
- `parts_agree` extracts both head and tail stateful transitions. It compares the head reads, obtains a frame between their actual middle states, derives Total for the actual left middle state through `part_frame`, and applies the tail induction there. It then rewrites only the pure list-result states. No desired output or canonical-current assumption enters the proof.
- `parts_transport` first constructs an actual right head transition to `rightMiddle`. Its tail induction uses that SAME `rightMiddle`, alongside the actual left head endpoint `leftMiddle`. The final frame relates the actual tail endpoints. It does not restart the tail in the initial right state or substitute an independently selected equivalent state.
- The common right bound is `firstFuel + restFuel`. `part_moreFuel` raises the head's bound by the tail bound while retaining its exact result and exact `rightMiddle`. `retains_mapM` raises each tail read by the head bound while retaining the exact `rightLast`; commutativity only aligns the numeric sum. Thus the constructed head and tail still compose through the actual middle state. Empty traversal uses zero. No equal-fuel-across-forests premise or unconditional callback termination claim is added.
- `resume_frame` carries the complete `Frame before previous` invariant through every read, transfers Total through that frame, and composes the final pure frame. This preserves counter, every stored value, residual obligations, both ancestry fields, and all representative/size reachability facts. It allows the parent forest representation to change by compression.
- `resume_agrees` accepts independent actual successful resumes at separate fuel bounds and gives identical optional pending output plus the complete final frame. `resume_transport` constructs one finite right success from one actual left success, input Frame and left Total; it does not require desired right success. `resume_moreFuel` retains the exact result AND the exact complete final state at increased fuel.

The two explicitly named local Monad/LawfulMonad instances use the established List proof pattern and support `List.mapM_cons` under the existing action representation. The selected inventory is one private definition, seven private proof lemmas, the public `resume` definition and four public theorems. The source adds no Safe, Ready, completion, canonical-current, right-success or pruning-soundness premise. It proves properties of successful modeled actions; it does not compare all error branches, count native executions, or establish native resource costs.

The supplied matcher is the reviewed 90-line candidate2, SHA `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509`. Its branch precedence, malformed-shape handling, prefix lengths and pending order remain unchanged. This review does not prove native representation refinement, correct template production, pruning soundness/completeness, driver equivalence or root-canonicality preservation. Those boundaries remain separate.

## Frozen inputs

All six owner payload paths and their bytes/hashes match the safe relative object-pin manifest. The complete package file set excludes only the exact top-level `pins.json` and `FROZEN.json`. Nested controls would remain payloads. FROZEN's manifest digest, six-file count and selected source identity match. All nine live input identities recorded by the source index match their current bytes. The retained uncompiled keyword-binder preflight draft/patch remains an author preflight, not a proof or native failure. No owner file was changed.

| Inspected input | Full bytes / SHA256 | Exact cuts / SHA256 |
| --- | --- | --- |
| `/tmp/mcfta-pruning-resume-20261024-resume-proposal/SourcePruningResume.lean` | 15277 / `593d1b84050ba85d130f32a57947be90374b29f66ca9a649a1070855757d024d` | 1–242: `593d1b84050ba85d130f32a57947be90374b29f66ca9a649a1070855757d024d` |
| `/tmp/mcfta-pruning-resume-20261024-resume-proposal/self-review.md` | 3304 / `060a68a2ccdd2b5ed54c24c0e8c39a099e36ec9368a9b9cea6b954622d1ad468` | Complete metadata/self-review |
| `/tmp/mcfta-pruning-resume-20261024-resume-proposal/pins.json` | 820 / `0130d3e846080ed1622c7a06518716ecd2967dd842634ab5f664f664e38fa076` | Complete metadata/self-review |
| `/tmp/mcfta-pruning-resume-20261024-resume-proposal/FROZEN.json` | 674 / `23ca2eef46eadfc2aa0a8c8cdcd62273e839a3e38449d54da293be829e61665b` | Complete metadata/self-review |
| `specftacular/src/Specftacular/Pruning.hs` | 16989 / `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` | 289–297: `101d4649504a7070ff4238b2e29a49000b3dd89e530a2ecfb78387ecc490aeee` |
| `lean/MicroCFTA/SourcePruningPartialMatch.lean` | 3692 / `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509` | 1–90: `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509` |
| `lean/MicroCFTA/EnumerationObservations.lean` | 6136 / `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab` | 31–48: `fb60a9b430b2238ac9694b06429de34c4de13827ff9319c34207650ac717a7d6`<br>69–81: `4a376930a8058c087d89d7d03d02cf95d224e02ad19adde13e9059f7cfbcaabf` |
| `lean/MicroCFTA/EnumerationCompressionFrame.lean` | 8220 / `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` | 20–76: `189efc8981290099e8321cf17a7dbf58cd46b1814e7140c823f30d0513aaa554` |
| `lean/MicroCFTA/EnumerationExecution.lean` | 30176 / `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` | 34–60: `837af9a7be1f3965d668270aad0744c1817adcae0f3d7015a09074b258238ab1`<br>98–105: `8331a5b424c96cec9da14b08730320a81fa24e9fb814d1f7e284356d5ddd2ba8` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 76898 / `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 1007–1010: `df00a8ec9a4b6df859f518918cafc3b50df35e221ceedd37b6862ffa98888d71` |
| `lean/MicroCFTA/EnumerationSchedule.lean` | 86287 / `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` | 1061–1079: `ef697e4c8bbdd0080d2123f784cd5ba4eae65772a0ba772392ff182322719605` |

# Real-prefix and opaque-expansion resource checkpoint

# Real-prefix and opaque-expansion resource checkpoint

Checked at 2026-11-15 23:40 CET. Checked code: `6efb9f31a15df30731fe1849b8db5b31cf0fc0d4`.
Prior checkpoint: `8f71f92d7e99b361ae664b4bcee721afd4e334d3`.
Source digest: `9fbd236afce040331d1405b9b6c08b28536f4bd56ae8e467d85bc1ddc6ba331d`. Main remains
`e53852064d3ef5a2eafec47d754c27504b11de5f` after the latest successful fetch.
No Haskell, Cabal, LiquidHaskell or tests changed. No Haskell fix is claimed.

The public theorem `prefix_real_narrowed_resources_at_original_budget` now
proves full CurrentPrefixResources for the actual successful nonempty
narrowed-Right prefix. It uses the SAME original workFuel, caller, heap,
complete cache, metadata, query and action. Its original header is byte-exact:
`9485965762b92593e8453286d6eb67c2fe1541e832f0cf74b0687477b91ccbc2`.
The proof derives a comparison bound internally. Replay can capture a different
action closure. The proof transfers only fields that do not depend on that
closure, then reconstructs the ORIGINAL action witness. It adds no future
resource, replay, bound or model premise. It does not increase runtime fuel.

The actual opaque/terminal helper also proves resources at every supplied
workFuel. Its success callback uses the genuine smaller-depth worker IH.
Actual empty-child rejection and stopped outputs retain their own resources.
An isolated proof established how to compare two generated matcher functions:
generalize the actual ChildDispatch result before cases on its returned value.
Then destruct the actual observation constructors. Each concrete branch reduces
by rfl. The tiny proof and the complete helper both passed strict checks.

All five publication gates passed in session 9111. Strict owner checks retain
all 66 old resource probes plus seven new probes: 73 standard-axiom reports.
Four independent normal imports passed. Audit checks 97,796 dependencies and
409 reports: 406 standard and three without axioms. Only propext,
Classical.choice and Quot.sound occur. The tree has 6,120 sources and 5,120
direct Audit imports. The old owner body remains byte-exact after one new
ordinary import. All other 6,117 old non-Audit sources remain byte-exact.

Original failed proofs, their repairs, exact sources and check logs are retained.
All earlier immutable checkpoints remain unchanged. The new archive excludes
compiled objects and contains no copied import overlays. Pinned source and
drivers reproduce the checks. Root has removed 227,063,896 bytes of known
terminal private objects in this run. Preserve live jobs, public .lake and
the five protected unknown tmp entries. Check exact sizes and liveness before
each cleanup. Heavy compiler jobs remain serial with 8 GiB caps and zero swap.

The whole identity-worker arbitrary-budget target c831 remains OPEN. Its latest
433-line candidate failed in session 83468 at the original 2,000,000-heartbeat
limit. The pure no-failed-callback control lemma passes. Prepared composition
and depth induction still time out during normalization. Failed elaboration
caused sorryAx reports in that PRIVATE candidate. The public tree and its
strict checks contain no such dependency. Source already contains six checked
task/scan components and the opaque helper. Append ONLY a repaired consumer.
Do not duplicate the components or weaken the original c831 header or budgets.

Next real-worker obligations: cover the actual remaining prefix branches and
derive genuine smaller-depth real callbacks. CurrentPrefixResources includes
CurrentPrefixFacts, which is False for stopped tags. Use the original resource
predicate for each actual branch. Do not assert this continuing predicate for
stopped runs. Keep all stop states, all emitted outputs and the original action.
The successful narrowed-Right theorem does not prove whole-worker coverage.

The native C/M theorem remains proved for ONE literal initial native node query
with both complete memo families empty. It preserves qualified structural
Profile at EVERY actual prefix with the original source, fuels and plans.
Profile permits Empty. Derive actual query occurrence qualification and original
InputsThrough/FieldsThrough from reservations. Extend the laws across requests
with inherited node/edge memo tables and domain cache. Do not reset those tables.

The FULL goal remains ONE finite accepted completion of the SAME original
emitted partial root under ONE compatible assignment satisfying actual native
domains, retained paths, UF aliases, residuals, readback, parked recompletion and
EVERY removed historical obligation on THAT output branch. Preserve the original
source/root/noStop, fuels, budgets, ALL outcomes and emissions before later stops.
Typing/depth adequacy and completeness, BOTH preprocessing/LPO language directions,
stream order/multiplicity/lazy demand, exact node-count/count/weight/training,
BOTH rank inverses, host bounds and compiled Haskell correspondence remain open.
Component resource proofs do not establish the joint finite witness.

Goal ACTIVE. Pushes to origin/formalize remain explicitly authorized. The fork
push was canceled as a wrong-chat request. Root owns Source/compiler/Git/board/tmp.
Primary usage was 30 percent at the latest observation. Pause and ping Matti if
it exceeds 80 percent. All earlier document bytes follow unchanged as history.



The checked source reproduces the Lean results. The pinned Nix shell and saved
public drivers give the exact commands. Run heavy jobs serially. This batch
uses an 8 GiB memory cap and zero swap. Earlier immutable checkpoints retain
their own exact compiler limits and results.

This archive contains lossless inputs, marked open targets, failed attempts,
repairs, and derived check logs. It contains no compiled objects, symlinks,
or copied import overlays. Historical private paths are not public build
requirements. Recreate private output paths and pins when repeating attempts.

archived-inputs.json maps each input to its original path, bytes and hash.
manifest.json covers every payload. verify.py checks decompressed inputs,
source digest, code patch, document reconstruction, and the manifest.
Use --current-tree only at the pinned source and checkpoint document state.

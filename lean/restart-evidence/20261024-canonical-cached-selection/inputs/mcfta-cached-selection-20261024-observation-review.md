# Cached selection and observing callbacks

Source review at 2026-10-24 01:28 CEST. Recommendation: add a pure canonical-cache selector and prove equality of its offered list with every successful old scan, with a strong compression frame for the returned state. Keep whole-driver correspondence separate until the actual observer primitives respect that frame. Class equivalence or the current `ReadOnlyOracle` premise alone is insufficient. No proof body, executable candidate, compiler command, native probe, or repository edit was authored or run by this reviewer.

## Actual source and existing models

Haskell `Enumeration.hs:827–834` only reads `_expandableUVars` and `_waitingUVars`. It returns Nothing when the candidate set is empty; otherwise it returns the ascending candidate set minus the waiting-map keys. It does not resolve a representative, compress a path, or write state. `nextExpandableUVar:855–869` preserves the completed-versus-blocked distinction and accepts a preference only when it names an offered candidate. Invalid preferences fall back to the minimum candidate. The stop test at 960–966 uses all candidates, before blocked keys are removed, and requires a nonempty set.

The source waiting counts are **canonical**, not raw. `writeUVarValue:450–466` maps each gained/lost suspended UVar through pure `UnionFind.root` before changing the count. Terminal equality merging at 733–746 moves the old root counters to the new representative. Counts include duplicates and omit zero entries.

There is one live namespace/file named `EnumerationIndexSelection`. The relevant existing layers differ:

| Model | What it actually proves or executes |
| --- | --- |
| `EnumerationWaitingIndex` | Counts raw `sc.var` occurrences. Its `Correct` equation is raw count equality, not the source's canonical count equation. |
| `EnumerationExpandableIndex` | Correct candidate flags and that raw waiting table; allocation, raw writes, and slot-preserving frames derive its invariant. Its frame permits any forest change when slots and counter stay fixed. |
| `EnumerationIndexSelection.findIndexed` | Folds representative-resolving actions over raw waiting keys. It still writes compressed forests and can report representative-fuel errors. |
| `selection_exact` / `selection_complete` / `reachable_selection` | Equal offered results for old and indexed scans, with canonical root maps preserved. Completion obtains a common sufficient finite bound. They do not prove equal final forests or model the current pure selector literally. |
| `EnumerationIndexSource` | Lifts actual assimilation to the raw-index mutation model and preserves raw occurrence multiplicity. It does not install the canonical source waiting invariant. |

These earlier results remain useful. `candidates_exact`, `scan_blocked`, `offered_congr`, and `findExpandable_exact` provide most of the offered-list argument. A canonical count view can group the existing raw occurrence counts by their actual representative. At selection time only canonical support is needed; maintaining writes and unions needs the counts themselves. Do not subtract existing raw waiting keys directly or rename the old indexed worker as the pure source action.

## Small compression frame

For the current `EnumerationState.State`, use equality of counter, complete value list, obligations, the entire raw-ID `recursionAncestry` function, and `expansionAncestry`. Permit different representative forests only when they have the same finite root information: for every UVar, root ID, and stored size, a `UnionFind.Reaches` judgment holds on one side exactly when it holds on the other. Keep Total/safety/domain conditions explicit where an operation needs them. This is a small sufficient frame for compression. It is not a claim to be the weakest quotient for every restricted client.

Root ID equality matters because callbacks return representatives and park checks by their numeric IDs. Stored root-size equality matters because union chooses its winner from those sizes, including the argument-order tie case. `UnionFind.findRoot_reaches_iff:211` already proves precisely the required root-information preservation under successful compression and Total. It is stronger than just SameClass preservation. Common `Roots` alone records the representative but existentially forgets its size.

`RenderStable` at `EnumerationDriver.lean:664–670` provides Safe after, equal counter/values/obligations, and SameClass equivalence. It omits both ancestry fields and does not state root-size equality. Its name does not make it a general observer or driver frame. With Safe on both sides, equal live payload slots constrain the possible root IDs; that does not supply the omitted ancestry or stored-size facts. `Safe` itself does not assert `UnionFind.SizesCorrect`.

Exact ancestry equality is a simple choice here. `checkRepeated` reads `recursionAncestry` at the current representative; `enumerateOutWith` installs expansion ancestry; allocation inherits it; assimilation unions old source and target ancestry. Keeping only live representative ancestry without a separate dead-entry proof is premature. Haskell uses sets for these keys; the current Lean model uses lists. A later source realization can weaken equality to the required set meaning, but that is a distinct relation.

## Concrete counterexamples to weaker claims

These are finite source/model derivations, not newly compiled theorems or native executions.

1. **Raw waiting subtraction gives the wrong candidate.** Let the forest have `2 → 1 → 3`, with 3 a root. Slot 0 is a pure unenumerated equality slot containing a suspended reference to 2; slots 1 and 2 are eliminated; slot 3 is an expandable ordinary node. The old raw waiting model stores key 2. Source canonical waiting stores key 3. Candidates are `[3]`. Subtracting raw key 2 incorrectly offers 3; source subtraction and the old resolving scan correctly report all work blocked. Both caches can satisfy their respective stated invariants.

2. **Even completion need not retain the exact forest.** Change slot 3 above to a pure equality slot with no node. There are no candidates. The source selector immediately returns Nothing unchanged. The old scan still resolves the reference from slot 0 and changes `2 → 1` to `2 → 3` before returning Nothing. No oracle is needed to show that literal full-state equality is too strong.

3. **RenderStable can change recursion decisions.** Keep the same safe forest, payloads, counter and obligations, with a ready recursive root 0 whose suspended reference names a separate pure root 1. Put its `recursionKey` in `recursionAncestry 0` on only one side. RenderStable holds in both directions because it ignores ancestry. `checkRepeated` returns true and clears constraints on one side, and returns false on the other. Similarly, changing only `expansionAncestry` changes the ancestry inherited by the next allocation.

4. **Same classes are not enough for representative observations or union.** Forests `0=root, 1→0` and `0→1, 1=root` describe the same partition but `getUVarRepresentative 0` returns different IDs. This is a counterexample to class equivalence alone; it does not assert that both forests satisfy equal live-slot payload constraints. More strongly, two forests can have identical singleton root IDs but root sizes `(1,2)` versus `(2,1)`. Union of 0 then 1 chooses different winners. The latter satisfies the model's Total/forest bounds and can satisfy Safe, which does not enforce correct class cardinality. It is not claimed to be a well-sized reachable Haskell state. Actual compression preserves sizes, so the proposed frame excludes it directly.

5. **ReadOnly is not observer congruence.** Consider `2→1→0` versus its compressed forest `2→0`, with all other state fields and root sizes equal. A modeled callback can read raw entry 2, return a pruning flag based on whether its parent is 0, and leave state unchanged. It satisfies `ReadOnlyOracle` exactly but returns different flags on the related states. Therefore that premise alone cannot justify changing the scheduler before an arbitrary callback.

6. **Same finite bound is not automatic.** On `2→1→0`, `findRoot 2` fails, while on `2→0` it succeeds with the same bound. A pure source selector does not perform that lookup at all. At sufficient bounds the representative agrees, but arbitrary same-fuel checked-result equality is false. This affects errors and can affect successful rows when a bounded callback itself performs the lookup. Existing termination and more-fuel lemmas support a sufficient-bound or explicit bound-adjustment statement. They do not supply a same-bound cross-forest theorem.

## Actual observer APIs and callback contract

The public enumeration module exports abstract `EnumerateM`, `getUVarRepresentative`, `getUnexpandedNode`, and `expandPartialTermFrag` (`Enumeration.hs:22–59`, 415–428, 1038–1046, 1412–1417). These helpers can compress paths. They preserve the intended returned representative/node/partial term under the stronger frame, subject to allocated-handle and sufficient-bound conditions in the checked model. They generally do **not** satisfy literal state-unchanged ReadOnly. Stored fragment and hole IDs must remain exact if returned terms and parked caller checks are to agree.

The public MonadState instance at 365–368 is also visible even though EnumerationState and its record fields are hidden. API visibility therefore does not enforce a read-only capability. A caller can save `get`'s opaque state inside an `EnumerateM ()` closure and later call `put` on that snapshot without naming the hidden type. This observation is a source-derived capability argument, not a tested native mutation witness. OrderedConfig's documented contract at 1327–1360 explicitly permits reads and alias compression and forbids allocation, merging, choice enumeration, and restoring old equality state. The general oracle type itself does not enforce those restrictions.

For driver composition, prove a relational observer rule for the actual public primitive programs. From paired framed states and equal callback input/caller state, the two successful output lists should have equal decisions and returned caller state, preserve order and multiplicity, and pair final machine states by the frame. If full checked errors are compared, add the actual error/bound clause. Frame preservation of each callback separately is not enough: the returned decision must also be invariant. If caller state stores opaque state snapshots, either restrict that behavior or state and prove a relation on caller states too. Do not assume this law for every inhabitant of Oracle.

The smallest next result is selection-level: the source-canonical pure selector leaves the full input state unchanged, returns the exact same offered list as any successful old scan, and the old scan's returned state differs only by the strong compression frame. Prove the frame through actual representative reads/folds using `representative_success` and `findRoot_reaches_iff`. Keep stop candidates separate from ready candidates. Then derive the concrete observing helpers' relational laws before attempting shared-driver correspondence. This requires no semantic acceptance oracle, new resource premise, or H23 wrapper.

## Upstream repair status

Local origin/main is `a5fbb66eec52b8c28a4beacd982f00626c9e279a`, the PR #168 merge of upstream fix `75cfc19b8`. The local merge `65f237954c3e867570c06d2de22681f55ca64fcd` and prior evidence commit `c841846eba7ab893460375a99a34e1d3f27ee9b0` have identical tree `e5c76044861f4945a83eea3351e61960d3515d7d`. No new native or Haskell bytes changed in this merge. During this review Root corrected the top FINDINGS index from local/import-needed to merged/no-additional-patch. I read the corrected index and its retained three-replacement record at `/tmp/mcfta-cached-selection-20261024/finding-status-change.json`. Both optional LPO defects remain open. No further Haskell repair is claimed here.

## Read scope and source identities

I read the whole live IndexSelection (232 lines), IndexSource (108), ExpandableIndex (179), and WaitingIndex (215). Other current reads cover State fields and primitive actions; Driver ReadOnly/checkRepeated/RenderStable; Schedule Roots/ScanValid/offered/exact scan and Safe; UnionFind root lookup/path/class/size/union statements; and the Haskell exports, state/cache updates, scheduler, observer helpers, and ordered-callback contract. Haskell eager/shallow loop and rendering ranges also reuse the earlier complete read at the unchanged file hash. This is not a whole manual read of EnumerationDriver, EnumerationSchedule, EnumerationExecution, or every imported proof.

| Live source | SHA256 |
| --- | --- |
| `cfta/src/Data/CFTA/Enumeration.hs` | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` |
| `cfta/src/Data/CFTA/Internal/UnionFind.hs` | `096db1d6a4d693cebfc9cb643486434baee93e3379c5a411d3edd556d102d434` |
| `lean/MicroCFTA/EnumerationIndexSelection.lean` | `ae067c7531435870f7c4fb84f13c93feced5c8f81cdd11fc621939fd77e9fcdc` |
| `lean/MicroCFTA/EnumerationIndexSource.lean` | `f3c6e8a698e457fcc8da637048049f1eec120f43ec8a208514e13410caba6e91` |
| `lean/MicroCFTA/EnumerationExpandableIndex.lean` | `b98e34950a8883a9152a24d97a3329e6d269dfb9c8c6e71c98ca10f27b682c11` |
| `lean/MicroCFTA/EnumerationWaitingIndex.lean` | `3dd9d39df6a289d3b9689280f0dbb786ea4609b8132016d1e4178d2ea9c0d8e5` |
| `lean/MicroCFTA/EnumerationState.lean` | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` |
| `lean/MicroCFTA/EnumerationDriver.lean` | `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf` |
| `lean/MicroCFTA/EnumerationSchedule.lean` | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` |
| `lean/MicroCFTA/EnumerationExecution.lean` | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` |
| `lean/MicroCFTA/UnionFind.lean` | `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14` |

H6 remains the strongest combined result. This report supplies a source-derived obligation map and counterexamples, not new checked theorems or whole-driver correspondence.

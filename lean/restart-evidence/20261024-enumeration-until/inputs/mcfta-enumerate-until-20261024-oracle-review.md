# Shared enumeration: oracle and rendering boundaries

Reviewed 2026-10-24 01:00:46 CEST. Read-only source assessment. No compiler, native probe, prepared program, Git mutation, network operation or repository write was run. The traces below are source derivations, not executed or proved results. Root may reproduce the finite examples with its serial capped probes.

**An unrestricted old/new no-stop bridge is false.** Keep the first bridge about the shared driver's no-stop, identity-narrowing, **eager `enumerateNode`** specialization. Do not substitute the public `termsPruneUntil` entry: it always selects shallow expansion. Successful-result equivalence, full error equality, callback-event equality and partial-renderer correspondence are different claims.

## Driver and callback order

Source `cfta/src/Data/CFTA/Enumeration.hs:905–1006` delegates `enumerateFully'` through `void (enumerateUntil' Nothing id-narrow enumerateNode ...)`. The previous main loop delivered `Right node` before `enumerateOutUVar` even for EmptyNode. The new loop applies narrowing, rejects EmptyNode, updates a changed node at its representative, and only then delivers `Right narrowed`. It preserves the repeated-recursion check before those operations. The expansion routine rereads the slot after the callback. Therefore a callback mutation can affect the actual expansion.

The stop test runs before node selection, narrowing, the EmptyNode test or oracle callbacks. It requires a nonempty `_expandableUVars` set and checks **all** its members. This set includes slots currently blocked by suspended dependencies. The scheduler separately subtracts `_waitingUVars` for ready selection (`827–870`). If all remaining slots are blocked and the stop rule does not accept them all, enumeration rejects as `ExpansionStuck`; it is not completed. If the rule accepts them all, it returns a partial state without discharging the dependencies. If no slots remain, it reports ordinary completion rather than an early stop.

### Counterexample 1: arbitrary modeled oracle revives an empty slot

`EnumerationState.Oracle` (`lean/MicroCFTA/EnumerationState.lean:297`) is an arbitrary enumeration-state computation. Choose graph node 0 empty and node 1 a single nullary `a` alternative. Start at node 0. On the old `Right 0` event, an oracle can `setValue uv (.unenumerated (some 1) [])` and return `(false, callerState)`; all other events simply continue. The old loop then rereads node 1 and can finish at `a`. The new loop rejects the initial empty node before invoking that callback. Thus equality for arbitrary model oracles fails even at the level of successful terms. This is a finite source/model trace, not a compiled theorem.

The actual Haskell export list (`Enumeration.hs:22–59`) hides `EnumerationState`, `UVarValue`, `setUVarValue`, allocation, union setters and the monad constructor/runner. It exposes abstract EnumerateM with its MonadState instance, plus representative reads, unexpanded-node reads and partial rendering. A client can use generic state snapshot/restore, but it cannot directly spell the hidden slot update through these exports. I have not claimed a direct public native setter witness. Conversely, the abstract monad type alone does not establish that every callback is read-only.

### Counterexample 2: successful-read-only is insufficient for full error equality

The existing `EnumerationDriver.ReadOnlyOracle` (`487–488`) says successful callbacks leave the state equal. An oracle that returns `failure .invalidSlot` on an empty-node observation satisfies that condition vacuously. The old loop reports that error before expansion; the new loop rejects the branch without it. Native Haskell also distinguishes a callback exception/divergence on this event from never calling it. Therefore read-only alone does not prove equality of all Except/error outcomes. A theorem about successful executions can ignore the differing error branch. A theorem about complete result/error lists needs a further condition that this skipped empty-node observation cannot produce an error or divergence.

For a first small bridge, `noPruning` has the existing `noPruning_readOnly` proof and no such callback error. Reusing ReadOnlyOracle for successful executions is a reasonable stronger restriction than merely requiring that an empty selected slot cannot be revived. Keep the statement honest about which outcomes it compares. Generalization to observing callbacks that compress union-find paths needs a suitable storage/frame argument; literal state equality is stronger than the behavior of every public read helper. Do not assume that RenderStable preserves arbitrary recursion-bookkeeping changes: its record does not constrain those fields.

### Counterexample 3: even a total read-only oracle distinguishes eager and shallow APIs

Use a finite unconstrained node `f[a]`. Let the oracle reject only `Left (TermFragmentNode "f" [TermFragmentNode "a" []])`, and otherwise return `(false, state)` without changing machine state. In the ordinary eager API, `enumerateNode` recursively prepares the child and delivers that complete root fragment, so the branch rejects. In `termsPruneUntil` with identity narrowing and a constantly false stop rule, `enumerateShallowHere` delivers `Left f[UVar1]`, then the child event `Left a[]`. Neither event matches the rejection, and final rendering yields concrete `f[a]`. All ingredients use the public callback/fragment API; no mutation or unsafe operation is needed. This trace follows `enumerateEdgeWith`, `enumerateShallowHere` and `prepareShallowChild` (`752–801`). It has not been executed here.

Thus a bridge for the shared eager specialization is separate from a shallow/eager language theorem. The latter needs no pruning, or an oracle contract that accounts for deferred observations and rejects the same complete candidates. ReadOnlyOracle by itself does not provide that observation compatibility. Shallow expansion also allocates ordinary-child slots that eager expansion does not, so do not promise identical counters, intermediate fragments or callback traces from a term-language equality.

## Partial versus complete rendering

`termsPruneUntil` (`1168–1193`) uses `rootTermFrag >>= expandPartialTermFrag` after either an early stop or ordinary completion. It does not search for an accepted completion of remaining holes. The confirmed retained native core probe already gives the decisive example: a true stop rule on EmptyNode returns the root `UVarHole 0`, although EmptyNode has no concrete term. This is the documented API contract, not an enumeration soundness result for completed terms.

`expandPartialTermFrag` (`1037–1046`) wraps actual symbols in ConcreteSymbol, follows enumerated fragments, renders an unexpanded recursive boundary with **no** suspended constraints as TruncatedRecursion, and renders every other unfinished value as UVarHole. It resolves representative storage for the read but retains the original argument UVar in a hole label. A constrained recursive boundary remains a hole. Arbitrarily forged invalid slots or cyclic fragment references are not made safe merely by using this diagnostic renderer.

The actual source's `recursiveBoundary` includes both InternedMu and InternedUnion (`Interned/Type.hs:608–611`). Do not replace that test with a Mu-only claim when mapping source nodes. An open union is retained until its references are bound.

`expandTermFragWith` renders any unexpanded recursive boundary using the caller's marker, regardless of the suspended-constraint list; an unfinished nonrecursive child raises its explicit error. `expandUVarWith` instead rejects an unfinished nonrecursive root (`1049–1075`). Those two failure behaviors are distinct. A well-formed completed driver state is what rules out inappropriate unfinished cases. There is no unconditional erasure from arbitrary partial output to a successfully accepted concrete term. In a settled state one can interpret ConcreteSymbol as its symbol and TruncatedRecursion as the caller's marker; an unresolved UVarHole needs an additional completion argument.

## Existing Lean helpers and their exact scope

| Existing helper | Reuse and boundary |
| --- | --- |
| EnumerationState.expandPartial (`342–354`) | Already models Concrete/hole/truncated rendering, including a constrained recursive node as a hole. It is a definition, not a proof that every partial result has a completion. |
| EnumerationState.constrained_recursion_is_hole (`657–661`) | Exact checked existing example for pending recursion. repeated_recursion_clears_constraints (`652–655`) covers the old complete driver clearing a repeated-recursion key before marker rendering. |
| EnumerationDriver.Finished (`540–541`) and findExpandable_finished | Finished means all slot candidates are ineligible. It is stronger than there being no currently unblocked candidate. Keep blocked and completed cases separate. |
| EnumerationDriver.ReadOnlyOracle / noPruning_readOnly (`487–493`) | Existing successful state-preservation restriction. It is not a guarantee of total/no-error callbacks or eager/shallow observation compatibility. |
| EnumerationDriver.getValue_storage (`680–692`), expandFragment_storage (`704`), expandUVar_storage (`755`) | Reads/rendering preserve stored values, supply, obligations and equality classes through RenderStable. The actual forest can be compressed. |
| EnumerationRendering.RenderReady (`35–39`) | Requires Safe, Finished, ReferencesCarry and Stratified. A stopped partial state is not automatically RenderReady. |
| EnumerationRenderability.completed_carrier (`227`) | Under CompleteGraph, Safe, Finished and CarriesGraph, the representative stores an enumerated fragment. CompleteGraph excludes recursive node views and requires valid edge equalities. |
| EnumerationRendering.getEnumerated_terminates (`49`), expandFragment_complete (`64`), expandUVar_complete (`128`), renderObligations_complete (`145`) | Supply finite rendering witnesses under their existing readiness/reference/strict dependency-level premises. They do not prove arbitrary stopped-hole completion or unrestricted source correspondence. |
| EnumerationOrder.Stratified (`18–23`) | Strictly increases stored-fragment dependency levels and puts pending roots at the frontier. This provides the finite rendering argument; arbitrary callback graphs need not satisfy it. |

Recommended first target: model the actual shared loop and show successful no-stop/eager executions agree with the preserved old eager loop for the ordinary noPruning observer, or a precisely stated observing restriction. Add the empty guard and exact callback order to the new source equation. State the speculative partial-result contract separately. Do not discard the existing old-driver theorems or present one finite probe as a general bridge.

## Inspected identities

- `cfta/src/Data/CFTA/Enumeration.hs`: 71269 bytes, SHA256 `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.
- `cfta/src/Data/CFTA/Interned/Type.hs`: 36883 bytes, SHA256 `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77`.
- `lean/MicroCFTA/EnumerationState.lean`: 33489 bytes, SHA256 `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.
- `lean/MicroCFTA/EnumerationDriver.lean`: 52410 bytes, SHA256 `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf`.
- `lean/MicroCFTA/EnumerationRendering.lean`: 13057 bytes, SHA256 `be611f9aa9e285872251ad14a40126fa358f393520f14576c9770ffa959db1a9`.
- `lean/MicroCFTA/EnumerationRenderability.lean`: 17735 bytes, SHA256 `604c62f77393a880d3a99d6924eb73f7f77aec7a374a56178facc5ed98ff11fa`.
- `lean/MicroCFTA/EnumerationSemantics.lean`: 42969 bytes, SHA256 `69ef14d4cfe44c8d448b5ea1a0521526f654caabd6e12b126463344733ad3a62`.
- `lean/MicroCFTA/EnumerationOrder.lean`: 23066 bytes, SHA256 `ba321f3490d5e0884bcdd538efd4ee4e600de765185137b49f3e7f538b39754b`.

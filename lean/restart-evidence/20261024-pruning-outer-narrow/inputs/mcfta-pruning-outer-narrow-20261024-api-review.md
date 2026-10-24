# Outer narrowing API review

CLEAR for the bounded Value-level source route at 2026-10-24 07:16:35 CEST. This is an independent source/API assessment, not declaration acceptance, a proof body or compiler evidence. I did not author the plan or the new declarations. Arity owns those declarations; Root owns the mathematical bodies and operations. I previously authored position helpers and FULL-tool adapters and reviewed the installed native narrowing components.

The complete plan `/tmp/mcfta-pruning-outer-narrow-20261024-plan.md` is 12212 bytes, SHA-256 `434c9435bb7248ecd5142d26b7df4de25d2b0bcbf5c02ac7389f80fcb7759bf9`. All 15 source identities in its table match the current files. No concrete source/API blocker was found. The exact packet must retain the restrictions below.

## Actual source inputs and branch order

`Pruning.hs85–99` publicly accepts `holeKey : t -> Int -> k`, `fits : k -> Symbol -> Bool` and `admits : k -> Node Symbol -> Bool`. Thus the same callback parameters are genuine operational inputs. They need no assumed output equation or semantic pruning law. The native `Hashable k` constraint supports the memo table; this Value-level model does not establish that table's behavior or extraction.

`Pruning.hs127–140` first matches `Mu`, then tests the ORIGINAL raw `uvarToInt uv` in the incoming `types`, then delegates to the local memoized `narrowAt` at `holeKey typing (uvarToInt uv)`. Keep that order. The Mu branch and the type-member branch return the complete original value and the same heap. Neither branch invokes a modeled reader or constructor. The fallback must return the complete existing `MergedSourceComparison.Result`, including its actual failure heap.

`SourcePruningRecordTypes.Metadata Typing` already contains `pending`, `types : List Nat`, `openHoles` and `typing`. Read `metadata.types` and `metadata.typing`. Do not call `updatedTypes`, select replacement typing, or use a representative root in membership/key selection. The wrapper does not update metadata. It needs no enumeration state or EnumGuard. No new carrier, graph, relation, predicate, monad instance or callback framework is required.

The Mu pattern uses `matchMu`, which returns `Just` only for `InternedMu` (`Type.hs767–784`). `recursiveBoundary` also accepts `InternedUnion` (`608–611`), so it cannot implement this branch. A non-type union must delegate. Empty and reference cases also follow the literal membership/fallback rule; finite completion premises remain separate.

## Existing API map and finite packet

- `InternedConstructorTemplates.Value` at22–27 has five constructors: empty; reference; node; union; and `mu (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depthShape ordinaryShape : Value Symbol NativeGuard)`. Preserve all three Mu payloads. There is no generic one-field Mu payload in this model.
- `MergedSourceComparison.Result` at23–25 already supplies `.done value heap` and `.failed fault heap`. A direct delegated equality preserves both forms. There is no reason to add a new result carrier or to prove failure preservation by running a second action.
- `SourcePruningNativeView.narrowAt` at33–44 takes the native EdgeKey equality, the two callbacks, fuel, key, complete Value and heap. It maps unresolved, pending and exhausted reader outcomes to their actual fault/heap. Its successful constructor uses the returned middle heap.
- `SourceEqualityRequiredCache.pure_keeps heap ready` at36 supplies `Keeps heap heap` for either bypass. It needs only initial `Ready`; returning `.done` is a result constructor, not a use of a List monad.
- `narrowAt_complete` at60–79 takes `Ready heap`, `Available heap oldValue` and `oldValue.free = []`. It derives one actual finite read/filter/construct run, result/after, `Keeps heap after`, availability and closedness, plus the SAME result and after at `fuel + extra`. No callback laws, desired final certificate or separate resource premise occur in this theorem.
- `Keeps.ready` is already final readiness; initial coherence is `ready.semantic.1.normal.facts.coherent`. Do not add either as an independent stronger premise.

For a combined finite wrapper theorem, choose fuel0 in either bypass and retain exactly `(oldValue, heap)` at every larger bound. In the fallback, specialize `narrowAt_complete` ONCE at `holeKey metadata.typing uv`; keep its fuel, result and full after. Retain `Keeps`, availability, closedness and larger-fuel equality. These three branches suffice. There is no induction or helper obligation.

Do not expose `Ordinary result` in the combined conclusion. `SourceEqualityRequiredCache.Ordinary` at68 includes only empty/node. The arbitrary-value type bypass may return a union or Mu, and the Mu bypass always retains Mu. The fallback's stronger ordinary/filtered-row results remain available inside that branch. Do not claim that equal returned handles imply equal native heaps after a fallback.

## Membership and constructor simplifiers

The model already uses `metadata.types.contains uv`. Branch correctness needs neither canonical order nor uniqueness of that list. With Nat's existing lawful equality, current Lean4.34.1 supplies `List.contains_iff_mem` (`Init/Data/List/Lemmas.lean523`) and the simp theorem `List.contains_eq_mem` at533. The latter states `as.contains a = decide (a ∈ as)`. It permits a public `uv ∈ metadata.types` premise or its negation to discharge the Bool branch without a new membership helper. Avoid deprecated `List.contains_iff`.

For a non-Mu hypothesis, reuse the existing NativeView pattern: `∀ entry body depthShape ordinaryShape, value ≠ .mu entry body depthShape ordinaryShape`. Case analysis on the five actual constructors eliminates only the Mu case with that hypothesis. It must retain union as a delegation case. Constructor-separated Mu/member/delegation equations and the existing `List.contains_eq_mem` should suffice; no `Value` equality instance is needed for the match. The explicit existing `[DecidableEq (EdgeKey Symbol NativeGuard)]` is needed for delegation, not a new `[DecidableEq Key]` or `[DecidableEq Typing]`.

When a conditional needs an explicit rewrite, current core provides `ite_eq_left` and `ite_eq_right` (`Init/Core.lean1179,1188`). `if_pos` and `if_neg` are deprecated there. Keep all-linter defaults. No locally ascribed helper, new instance or global simplifier is required by the inspected API. These are source-derived elaboration recommendations; no candidate was compiled during this review.

## Later coupling and explicit boundaries

Derive the complete old Value from the SAME first pending `getValue` slot and incoming `PendingRealized` before inspecting its constructor. `lookup_encode` supplies its encoding from actual lookup and Ready-derived coherence. The existing read frame and the intervening frame compose to the entry state E. A bypass keeps E, not an earlier forest, and uses `pure_keeps` plus `realized_preserved` to retain every slot. It executes no second representative action.

Only the fallback uses `narrow_pending_complete` with the concrete key. Its existential oldValue can be identified with the classified value through functionality of the SAME `lookupNode heap oldHandle`. That is proof witness identification, not a second computation. The changed surviving branch already carries actual E→Q representative effects and the exact Q→F write of the derived result with the same scs. Original uv remains the membership/key input; the canonical root is the write destination.

Keep Empty rejection BEFORE the equal-handle branch in the eventual driver. A type-position bypass can return Empty, so bypass success alone is not an accepted enumeration branch. `EnumerationUntil` at108–119 tests `graph.node narrowed` for Empty before handle equality and the changed write. Its narrow callback still returns a pure Nat and has no explicit native heap: this wrapper does not by itself instantiate that driver or justify graph classification. `narrowAt_empty` remains available for a delegated Empty case without Ready; no new equation is missing.

The concrete Specftacular caller at1108–1116 uses `canonicalVariables (holeTypeOf typing rawID)`, `constantFits typeDepth skeletonSig` and `flip typeAdmits`. Native `PartialTyping`, substitutions, unification and instance-depth checks are real mechanisms (`Types.hs975–1009`). `typeAdmits` explicitly ignores node constraints (`Utils.hs229–245`). An exact-name search found none of those six typing/key helper names in current MicroCFTA sources. `SourceTypingRules` instead models abstract resolved rule rows, not that substitution/unification implementation. Do not infer semantic typing preservation, key equivalence, native memo correspondence or pruning soundness from the operational callback parameters.

Native raw Int/UVar↔Nat conversion, IntSet representation, native NodeId↔model handle encoding, cached-index maintenance, graph extraction and a heap-coupled driver remain separate. No actual action, H6 strengthening, solver, whole-pass or convergence result is added. The plan's70–115 estimate/hard140 for the finite packet is plausible from these existing APIs, subject to the separate exact declaration and body gates.

## Read scope and exact identities

The plan was read completely. The cuts below were inspected in this review; small previously reviewed sources retain their live identities. I do not claim a full manual read of the large Haskell files or a new proof review of the full import closure. Only this review file was written. No compiler, prepared program, Git/network, board or repository write occurred.

| Defining input | Read cut | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `specftacular/src/Specftacular/Pruning.hs` | 85–153 | 16989 | `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` |
| `specftacular/src/Specftacular.hs` | 1094–1122 | 77825 | `b5a19e8c83908ff2de3cf3ee704731733224d96f36b7fb597afcd0fa017dbace` |
| `specftacular/src/Specftacular/Types.hs` | 800–820;970–1012 | 57422 | `e559f049d1f1c4397606e36580322ae5d3f256f1601a8d481ec25a1f4e429119` |
| `specftacular/src/Specftacular/Utils.hs` | 225–247 | 9246 | `2737df7df4bce7178e45c96db3bf550a0ce4c2d7d57ed131e2689071ec2e53ec` |
| `cfta/src/Data/CFTA/Interned/Type.hs` | 275–298;357–371;604–615;667–679;762–788 | 36883 | `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77` |
| `lean/MicroCFTA/SourcePruningRecordTypes.lean` | 1–108 | 13138 | `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf` |
| `lean/MicroCFTA/SourcePruningNativeView.lean` | whole177 | 10881 | `0cf2d0d30d1a231dd6a1c53dc8a78bc0b8c37972ff5fe3d55b2767e9f6f98571` |
| `lean/MicroCFTA/SourceEqualityRequiredCache.lean` | whole105 | 6081 | `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733` |
| `lean/MicroCFTA/InternedConstructorTemplates.lean` | 1–140 | 46073 | `75aeb072ce0cfb7bc8bad40843184743281de8aeac1001c13ad941692d23e3f8` |
| `lean/MicroCFTA/MergedSourceComparison.lean` | 1–55 | 5587 | `215330f70fa1b4ad03924607a653c5ebce213f866f2cc1f588a3b25ce25132fc` |
| `lean/MicroCFTA/SourcePruningPositions.lean` | 1–125 | 11125 | `f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d` |
| `lean/MicroCFTA/SourcePruningTemplates.lean` | 1–45 | 8380 | `1890878e308ec4debe67d6e74755bc00d93898f59a3a4ed1e5fa188c02899156` |
| `lean/MicroCFTA/EnumerationUntil.lean` | 94–130 | 8864 | `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137` |
| `lean/MicroCFTA/SourceTypingRules.lean` | 1–40 | 7561 | `883358821462c869be1ed01b284c674b62d5fa6519495661cd89e4bcb305fdc1` |
| `lean/MicroCFTA/SourcePruningEnumerationNarrowing.lean` | whole104 | 7246 | `b1cfefb6d6907cd871cfe7dd345caaadbc4ba67d3f2e1067de14f72bba793559` |
| `lean/MicroCFTA/SourcePruningEnumerationIdentity.lean` | whole58 | 2939 | `e260eceaa5ed848c94155530c24ccca7c99092db0091b8b9e6174c33894e7361` |
| `lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | 15–70 | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` |
| `lean/MicroCFTA/SourcePruningEnumerationNodes.lean` | 2–45 | 3546 | `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4` |
| `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Data/List/Lemmas.lean` | 517–543 | 152710 | `9f9177396114b7b5898b0c4ac95f91bb3ee139f16dcde3becabdf9f948170dda` |
| `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Core.lean` | 1170–1195 | 100653 | `6218a9825a0ce51a6bbe3949ec7a86c4406f4f216bd3cd1262736cfc1c997c54` |

Read-only diagnostics: two guessed local core file paths were absent; the installed4.34.1 paths above were then read. An aggregate tool result was truncated, so the missing membership/core and driver cuts were read separately. These are review-tool diagnostics, not Lean or Root job failures.

# Enumeration node handles and the concrete pruning callback

Recorded 2026-10-24 04:49:23 CEST. Read-only source assessment. No compiler, prepared program, Git command or repository write. The native-view declaration author wrote this plan. Root authored and installed its actual proof. This is API correspondence and next-scope planning, not an independent reproof of those foundations.

**Recommendation:** first add a small computed handle/readback module for the actual `InternedConstructorTemplates.State`. Then use it in one literal `typedTypes` callback with an explicit constructor-heap result. Do not replace the old enumeration Graph or assume a caller-supplied node decoder. The callback composition does not require a complete new enumeration interpreter.

## The two IDs are different

Native Enumeration.hs185–195 stores `Maybe (Node symbol)` in an unenumerated UVar. Its public observer1412–1417 returns that actual node after representative compression; it does not return `nodeIdentity`. The modeled `EnumerationState.UVarValue`29–33 instead stores `Option Nat`, and `EnumerationNodeObservation.getUnexpandedNode`19–22 returns that graph handle. A raw UVar ID selects a slot; the optional node handle names the automaton value stored in that slot. Preserve raw UVar IDs for `holeKey`, type/open membership and program-hole labels. Never apply `holeKey` to the graph handle or its canonical node entry ID.

The existing bounded-row modules do not close this gap. EnumerationInternedRows16–28 uses `Cache.State (List (EnumerationState.Edge Symbol Guard))`. EnumerationBuilderCaches88–108 uses its own edge/node caches and shifts a stored node ID by one because handle zero denotes Empty. Neither is `InternedConstructorTemplates.State`, whose cache payload includes ordinary, union and Mu records and repaired unfolding. EnumerationBuilderRuntime265–267 exposes only empty/ordinary alternatives. Its graph theorem is not a decoder for the native-view Value.

## Smallest concrete next component

Propose `SourcePruningEnumerationNodes`, importing `SourcePruningNativeView` and `EnumerationNodeObservation`. Use the existing full Symbol alias. The following are proposed bare interfaces, not compiled declarations:

```lean
def encodeNode (value : InternedConstructorTemplates.Value Symbol Guard) : Option Nat

def lookupNode (heap : InternedConstructorTemplates.State Symbol Guard) (node : Nat) :
    Option (InternedConstructorTemplates.Value Symbol Guard)

theorem available_readback
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (value : InternedConstructorTemplates.Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value)
    (closed : value.free = []) :
    ∃ node, encodeNode value = some node ∧ lookupNode heap node = some value

theorem lookupNode_keeps
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (kept : SourceEqualityRequiredCache.Keeps before after)
    (node : Nat) (value : InternedConstructorTemplates.Value Symbol Guard)
    (present : lookupNode before node = some value) :
    lookupNode after node = some value
```

`Symbol` in these proposed interfaces abbreviates `SourcePruningTemplates.Symbol`; `{Guard : Type}` is the native constraint parameter. No new Symbol or node datatype is needed. No constructor comparison instance is needed merely to read these fields; use existing Nat equality for the winner check.

Choose the already used empty/positive handle convention, subject to Root approval: Empty encodes as zero; node/union/Mu encode as their entry.identity+1; reference encodes as none. This is a model handle convention, not an assertion that Haskell's raw NodeId is incremented. Native Type.hs361–367 has no nodeIdentity for Empty or unresolved nodes, so mapping every Value directly to its raw ID would be incomplete. Native ordinary/union/Mu entries share nodeIds459–468; no dense-ID premise is justified.

Define lookup by actual tables. Zero returns some Empty. For successor identity, read heap.nodes.issued identity; read the canonical entry from heap.nodes.table at that key; require its identity equals the requested identity; then read heap.nodeRecords at that key. Each missing step returns none. **Do not use issued→key→nodeRecords alone.** Cache.State128–138 explicitly retains issued candidates that can lose races. Such a reservation can share a key with the winning payload while having a different identity. The canonical winner check prevents that wrong-ID readback. It also keeps missing/pending payloads distinct from Empty.

Proof route: available_readback cases on Value. Empty is direct; reference contradicts closed; the three stored constructors use Available.resident, InternedFreshProbeKeys.resident_entry and Coherent.valid.2 to derive the exact issued key, canonical entry and complete stored payload. The existing resident_identity_unique45–54 proves the relevant full-record uniqueness from coherence without a new Constructed premise. For lookupNode_keeps, unfold a successful lookup and use its issued-history extension plus Grows.nodes and Grows.nodeRecords. No new replay law is assumed.

Expected complete source: about75–115 lines, proposed hard140. Publics: two pure definitions and two theorems. No induction beyond constructor cases, no new packet type, no arbitrary decoding callback. A later exact declaration gate must pin the actual local/case inventories before Root writes bodies.

## What this enables, and what still needs a producer

Use one explicit slot invariant as a reviewable predicate, not a new record: every stored `.unenumerated (some node) scs` has a Value with `lookupNode heap node = some value`, `Available heap value` and `value.free=[]`. It is a relation over the actual computed lookup, not a supplied map or a final-success certificate. An actual closed original build plus available_readback derives it for `EnumerationState.initial node`. Full Frame.values equality preserves it through representative reads; lookupNode_keeps plus Available.grows preserves it through native heap growth. Deriving it after ordinary-child allocation, actual intersection/assimilation and the driver's narrowed-node write remains an explicit later obligation.

Ready by itself does not make every cached record closed. It contains genuine open binder probes and shapes. The pending-slot closedness must come from the source operation that placed that Value in the slot. StorageValid bounds UVar slots, suspended references and the forest, but its SlotBound case deliberately does not validate the stored automaton handle. Neither existing property is an ID-realization theorem.

`getUnexpandedNode_success`24–37 already inverts the actual modeled read to its representative slot. With the slot invariant it supplies the exact native Value for a returned some handle. `getUnexpandedNode_agrees`40–53 and transport56–67 retain all final enumeration fields through Frame. Use independent successful bounds; do not assert equal fuel for compressed forests. A finite-read producer can use StorageValid, an allocated raw hole `h < counter`, UnionFind.findRoot_terminates, findRoot_bounded875–899 and getValue_success1018–1035. Total alone does not guarantee that the returned root has a stored slot.

## Literal typedTypes composition

The remaining callback is not just index realization. Source Pruning113–125 calls recordTypes once, tests **incoming** raw type membership, performs a fresh second partial render only for an unpruned program-position Left event, and calls the actual public extend on openProgram False. A failed extension returns `(true, state')`. On success, delete the current raw ID from open first, then insert programHoles in source right-fold order. Observe the resulting ascending unique open set. Read **all** its nodes in order, including after an earlier dead result; only then apply pure `or`. A missing pending node contributes false. A Mu value contributes false. Union must use the actual repaired closure, not the Mu exemption. A dead result returns the recorded old typing/open metadata; compression effects already made by the reads remain.

Reuse SourcePruningRecordTypes.recordTypes, SourcePruningPositions.openProgram/programHoles, and the installed SourcePruningNativeView.emptyAt_complete/mu. Do not repeat templateOracle manually. Keep the public source functions `extend`, `holeKey`, `fits` and `admits`; no supplied `emptyAt` callback or desired-result law is needed. Literal composition and observation congruence require no typing-soundness or monotonicity oracle. Those stronger pruning-language properties are separate.

The constructor heap has to be retained somewhere: EnumerationState.State73–80 has only UVar state, forest, obligations and two ancestries. It cannot silently carry the heap changed by repaired Mu exposure or makeNode. A minimal explicit callback can take the initial native heap and return an existing `MergedSourceComparison.Result Symbol NativeGuard (Bool × Metadata Typing)` inside the existing `EnumerateM Symbol EnumGuard`. Its done/failed carrier holds the exact native heap; the EnumerateM success holds the exact compression state. Thread the native heap through all open-hole checks. This is a proposed interface choice, not an implemented adapter. Keeping EnumGuard and NativeGuard distinct avoids equating residual enumeration obligations with full interned edge constraints.

During this callback the ordinary enumeration values do not change: only rendering and getUnexpandedNode compression occur. Therefore existing node-handle lookups stay valid while the separate constructor heap grows. A fixed enumeration Graph can remain a parameter for this callback proof. Do not claim the coupled callback is the existing exact-state ReadOnlyOracle: Enum compression and native heap growth are real effects. The natural preservation result is full Frame on the enumeration core plus Keeps on the native heap; all metadata branches must remain exact.

Use a direct ordered list/map helper for the open-hole checks only if needed. Its invariant is full Frame from the incoming core, native Ready, Keeps from the incoming heap, and availability/closedness of the original pending Values under that growth. Mu checks are immediate; non-Mu checks use actual emptyAt_complete. For a sufficient common native bound, use the larger-bound narrowAt conclusion plus the derived all-bound ordinary second reader; emptyAt_complete alone currently exports only one successful bound. A small emptyAt larger-bound lemma can be derived before the batch. Enumeration getUnexpandedNode_moreFuel and expandPartial_moreFuel handle their own successful bounds. Existential finite bounds and preservation are separate from paired successful-run congruence.

## Modeling decisions that do not disappear into lookup

1. Approve the empty/shifted-positive handle representation and its explicit source NodeId correspondence. A raw UVar remains a different number. Reject absent/losing IDs instead of turning them into Empty.
2. Approve an explicit native-heap result for the callback. Placing it in a new global state framework is unnecessary; dropping its effects is incorrect. Haskell's process-global interning/memo2 realization remains distinct from per-call functional heap evidence.
3. Retain the existing Graph as an interface for the callback composition. A later genuine source graph bridge must derive constructor-child handles, path-equality tries and residual guards from the actual complete edge constraint. The old generic Guard field is not already that decomposition.
4. Do not equate Enum Node.recursive with native Mu: it is the renderer's broader Mu/union recursive boundary. MergedFreshOrdinaryGraph.graph27–29 is an EpsilonUnion.Graph indexed by Value, not EnumerationState.Graph indexed by Nat; it also observes actual repaired successor execution. A full evolving graph realization must account for those new heap values and actual intersection. It is not a renaming of bounded-row lookup.

The concrete next checkpoint should be the computed handle readback/growth component, followed by the small ordered observer/native-empty batch and then literal typedTypes. Full driver/cached-index realization, branch multiplicity, source error-stream correspondence, typing soundness, convergence and numeric runtime bounds remain separate. No replacement of the optimized Haskell core is indicated by this assessment.

## Verified live source identities and selected cuts

These hashes identify full files read at this cut. Cuts identify the declarations or source branches used above; they are not standalone snapshots or compiler evidence.

| File | Lines / bytes / SHA-256 | Selected cuts |
|---|---|---|
| `cfta/src/Data/CFTA/Enumeration.hs` | 1587 / 71269 / `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 185–220,228–260,416–445,780–798,950–1006,1412–1417 |
| `specftacular/src/Specftacular/Pruning.hs` | 350 / 16989 / `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` | 85–141 |
| `cfta/src/Data/CFTA/Interned/Type.hs` | 922 / 36883 / `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77` | 361–367,455–483 |
| `lean/MicroCFTA/EnumerationState.lean` | 699 / 33489 / `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 29–55,73–80,126–130 |
| `lean/MicroCFTA/EnumerationNodeObservation.lean` | 78 / 4323 / `0dc7f259885a4c5a914aed2d7a62030b18cc87fc37962ffe438c146b6459d06d` | 19–76 |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 1276 / 76898 / `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 631–650,875–899,1018–1035 |
| `lean/MicroCFTA/EnumerationCompressionFrame.lean` | 145 / 8220 / `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` | 20–53,80–89 |
| `lean/MicroCFTA/EnumerationObservations.lean` | 105 / 6136 / `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab` | 51–103 |
| `lean/MicroCFTA/EnumerationBuilderCaches.lean` | 451 / 27843 / `f4882be07a73362a667a994f9e37344b9fb4619565dcf53ca0e857ecd21ccb9d` | 88–108 |
| `lean/MicroCFTA/EnumerationInternedRows.lean` | 138 / 7727 / `ec138999e1de79ff0e51afa61d6cfa35e663c7b7cbd54938535c5fc0e922324e` | 16–28,50–55 |
| `lean/MicroCFTA/EnumerationBuilderRuntime.lean` | 559 / 34864 / `03857042a01483c406a7a941c6c082e9f897a8e07d8a0b3fab3fa91e21b86b98` | 16–34,265–281 |
| `lean/MicroCFTA/InternedConstructorTemplates.lean` | 805 / 46073 / `75aeb072ce0cfb7bc8bad40843184743281de8aeac1001c13ad941692d23e3f8` | 22–31,62–80 |
| `lean/MicroCFTA/Cache.lean` | 334 / 16352 / `139de1fc30ece4ef377ec87afd42d0b82ec57a01869339015e7eab21eece4215` | 124–138 |
| `lean/MicroCFTA/InternedFreshProbeKeys.lean` | 256 / 17295 / `dcb69b5fa5146bd0c690d871e3de9ad42420070aef17b0a489bfe2994bb7209b` | 14–54 |
| `lean/MicroCFTA/InternedProbeProvenance.lean` | 268 / 16949 / `9a0f3138d84df02b4aa36c754d7a19c995d2aacd120b5b35b190dfe0d7895ce1` | 19–25,40–60 |
| `lean/MicroCFTA/SourceEqualityRequiredCache.lean` | 105 / 6081 / `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733` | 18–40 |
| `lean/MicroCFTA/SourcePruningNativeView.lean` | 177 / 10881 / `0cf2d0d30d1a231dd6a1c53dc8a78bc0b8c37972ff5fe3d55b2767e9f6f98571` | 21–79,147–175 |
| `lean/MicroCFTA/SourcePruningRecordTypes.lean` | 209 / 13138 / `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf` | 26–60,112–209 |
| `lean/MicroCFTA/SourcePruningPositions.lean` | 209 / 11125 / `f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d` | 18–73 |
| `lean/MicroCFTA/EnumerationPartialObservation.lean` | 87 / 4692 / `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc` | 24–83 |
| `lean/MicroCFTA/MergedFreshOrdinaryGraph.lean` | 81 / 4336 / `00d74646b29174976b2fb0b65dd0af4ae309deee31d35ac8591fed6e303f99a4` | 16–29 |
| `lean/MicroCFTA/EnumerationUntil.lean` | 180 / 8864 / `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137` | 90–130 |

Direct usable imports for the first component: `MicroCFTA.SourcePruningNativeView`, `MicroCFTA.EnumerationNodeObservation`. Callback composition additionally uses `SourcePruningRecordTypes`, `EnumerationPartialObservation`, `EnumerationPartialCongruence`, `EnumerationPartialTransport` and the existing Schedule/Execution helpers through their imports. All import paths were read as local Lean files; no import was executed.

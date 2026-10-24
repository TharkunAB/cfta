# Actual pending-node observation from realized slots

Recorded 2026-10-24 05:04:53 CEST. Read-only planning. No proof body, compiler, prepared execution, Git operation or repository edit. The author proposed the codec declarations; Root authored its installed76-line implementation. This plan does not independently reprove that implementation.

**Recommendation:** one additive `SourcePruningEnumerationObservation` module with five declarations: one concrete pending-slot predicate, initial realization, joint frame/cache preservation, observed-node realization, and a finite observation producer. Use the existing observer unchanged. No replacement graph, default decoder, new state type or callback is needed in this component.

## Exact relation and proposed interfaces

Imports: `MicroCFTA.SourcePruningEnumerationNodes` and `MicroCFTA.EnumerationNodeObservation`. The codec is now installed at SHA1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4. The following are bare proposed headers. `Symbol` abbreviates the existing `SourcePruningTemplates.Symbol`; `EnumGuard` and `NativeGuard` are distinct Type parameters. These statements are not a body-authoring gate.

```lean
def PendingRealized
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : EnumerationState.State Symbol EnumGuard) : Prop

theorem initial_realized
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = []) :
    ∃ node, SourcePruningEnumerationNodes.encodeNode value = some node ∧
      PendingRealized heap (EnumerationState.initial node : EnumerationState.State Symbol EnumGuard)

theorem realized_preserved
    (heap nextHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (realized : PendingRealized heap before)
    (frame : EnumerationCompressionFrame.Frame before after)
    (kept : SourceEqualityRequiredCache.Keeps heap nextHeap) : PendingRealized nextHeap after

theorem observed_realized
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv node : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (realized : PendingRealized heap before) (total : UnionFind.Total before.representatives)
    (observed : EnumerationCorrectness.Success
      (EnumerationObservations.getUnexpandedNode fuel uv) before (some node) after) :
    EnumerationCompressionFrame.Frame before after ∧
      ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
        SourcePruningEnumerationNodes.lookupNode heap node = some value ∧
        InternedProbeProvenance.Available heap value ∧ value.free = []

theorem observation_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard) (uv : Nat)
    (realized : PendingRealized heap before)
    (storage : EnumerationCorrectness.StorageValid before) (inside : uv < before.counter) :
    ∃ fuel observed after,
      EnumerationCorrectness.Success
        (EnumerationObservations.getUnexpandedNode fuel uv) before observed after ∧
      EnumerationCompressionFrame.Frame before after ∧
      (∀ node, observed = some node →
        ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
          SourcePruningEnumerationNodes.lookupNode heap node = some value ∧
          InternedProbeProvenance.Available heap value ∧ value.free = [])
```

The concrete PendingRealized definition quantifies over an actual index `slot : Nat`, handle `node : Nat` and suspended list `scs : List EnumerationState.Suspended`. If `state.values[slot]? = some (.unenumerated (some node) scs)`, it requires an existential complete Value whose actual computed lookup is some that Value, which is Available in heap and has free=[]. Other slot forms impose no condition. It has no decoder parameter, supplied correspondence function, desired observed Value or desired final state.

The initial theorem must **derive** the handle using available_readback. The one initial pending slot stores that derived handle. Do not add an encode/lookup premise supplied by the caller. A successful some0 observation means the actual Empty Value; an observer result none means no stored pending node. They remain distinct.

realized_preserved rewrites the actual after-slot with Frame.values, obtains the earlier complete Value, applies lookupNode_keeps, and uses Available.grows with the same kept.growth and kept.history. The cached Value itself and its free field do not change. The full Frame premise retains the allocation counter, obligations, both ancestries, and exact root IDs/sizes; no forest equality is claimed. This theorem deliberately consumes actual Keeps, not assumed final lookup preservation.

observed_realized first inverts getUnexpandedNode_success24–37. Then getValue_success1018–1035 identifies the actual representative slot in before.values. Cases on the actual returned UVarValue and its optional stored node force the unenumerated/some case. Apply PendingRealized at that slot. The Value is an output. getValue_frame80–89 supplies the full final Frame under Total. There is no need for a graph, Safe/Ready-to-expand, Finished, representative-root premise or native Ready here.

## Why finite observation needs storage

Total before.representatives supplies a finite path, not a value-table entry. For example an empty forest and empty values list have a total default-root interpretation, yet getValue at0 has no slot. observation_complete therefore also requires an allocated raw uv and the existing genuine StorageValid packet. Its proof uses only storage.total, storage.forest and storage.aligned; the full packet is the existing producer interface, not a new state abstraction. An explicitly weaker theorem could take those three fields separately, but that is unnecessary for the first component.

Obtain `root,size,path` from storage.total uv, then `fuel,found,lookup` from UnionFind.findRoot_terminates path. findRoot_bounded875–899 gives found.representative<before.counter. SupplyAligned means before.counter=before.values.length, so the representative has an actual stored UVarValue. Define the output state by replacing only representatives with found.forest. getValue_success constructs the actual read. getUnexpandedNode_success constructs the actual optional-node observation from that same stored value and state. Apply observed_realized when its result is some handle; none needs no fake native Value. No hypothetical successful observer or final certificate is an input.

The only proof inventories needed are finite cases; no induction or IH is required. Planned local types: `root,size,fuel : Nat`; `path : UnionFind.Reaches before.representatives uv root size`; `found : UnionFind.Result`; `lookup : UnionFind.findRoot fuel before.representatives uv = some found`; `rootInside : found.representative < before.counter`; `storedValue : EnumerationState.UVarValue Symbol`; `stored : before.values[found.representative]? = some storedValue`; `after : EnumerationState.State Symbol EnumGuard` with its exact representative replacement; `observed : Option Nat` projected from storedValue. Observer inversion additionally uses the exact getValue Success and optional-node projection equality. The next exact declaration package must pin all such types and case attachments before a body is authorized.

Budget estimate: predicate/context10–15 lines; initial theorem+proof15–22; preservation15–22; observed realization25–35; finite producer35–50; comments/spacing10–20. Target120–165 ordinary lines, proposed hard180, no padding. Five public declarations, zero private helpers or new types. If compilation later requires a small list lookup fact, first use the actual stored-index library API; do not add a framework.

## Scope needed by the later callback

This module establishes initial realization and preserves it through the observation-only part of a callback and actual constructor-heap growth. It does not establish the relation after arbitrary allocate, intersectValues/assimilation or the driver's narrowed-node write. Those producers must use the exact computed codec and genuine closed-value construction results. Generic StorageValid checks UVar storage, not automaton-handle realization; native Ready permits open binder probe records, so it also cannot replace PendingRealized.

The complete typedTypes callback must separately preserve that every raw open-hole ID is below the allocation counter. StorageValid alone says nothing about an arbitrary Metadata.openHoles list. Derive this metadata bound from the source initial0, actual allocated fragment holes, deletion and source-ordered insertion. Keep holeKey applied to the raw UVar ID, never to its graph handle. This is different from native NodeId extraction or graph interpretation.

For the later batch, retain all ascending open-hole getUnexpandedNode actions and their full compression states before evaluating the pure or result. Native fmap/pure are lazy: or may demand only a prefix of the pure emptyAt calls. Preserve the separate constructor heap only for those demanded calls, and do not stop earlier UF observations at the first true Boolean. The frozen additive laziness caveat50920360... records this distinction. Error forcing for invalid values and complete native stream equality remain open.

Native emptyAt completion uses the actual existing SourcePruningNativeView, with its Mu-only bypass and actual second reader. EnumGuard remains separate from NativeGuard. This component adds no arbitrary emptyAt oracle, no replacement Graph, no new callback semantics, no typing-soundness law, no runtime bound and no claim of whole-driver correspondence.

## Exact current dependency cuts and full-file hashes

| File | Lines / bytes / SHA-256 | Used cuts |
|---|---|---|
| `lean/MicroCFTA/SourcePruningEnumerationNodes.lean` | 76 / 3546 / `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4` | 16–74 |
| `lean/MicroCFTA/EnumerationState.lean` | 699 / 33489 / `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 29–33,73–84,107–130 |
| `lean/MicroCFTA/EnumerationNodeObservation.lean` | 78 / 4323 / `0dc7f259885a4c5a914aed2d7a62030b18cc87fc37962ffe438c146b6459d06d` | 19–76 |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 1276 / 76898 / `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 154,631–650,875–899,1018–1035 |
| `lean/MicroCFTA/EnumerationCompressionFrame.lean` | 145 / 8220 / `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` | 20–53,80–89 |
| `lean/MicroCFTA/UnionFind.lean` | 808 / 41077 / `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14` | 160–179,201–219 |
| `lean/MicroCFTA/InternedProbeProvenance.lean` | 268 / 16949 / `9a0f3138d84df02b4aa36c754d7a19c995d2aacd120b5b35b190dfe0d7895ce1` | 19–25,40–60 |
| `lean/MicroCFTA/SourceEqualityRequiredCache.lean` | 105 / 6081 / `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733` | 18–40 |
| `lean/MicroCFTA/SourcePruningRecordTypes.lean` | 209 / 13138 / `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf` | 26–60 |
| `specftacular/src/Specftacular/Pruning.hs` | 350 / 16989 / `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` | 107–141 |
| `cfta/src/Data/CFTA/Enumeration.hs` | 1587 / 71269 / `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 328–351,416–432,1412–1417 |

Additive laziness note: `/tmp/mcfta-pruning-enumeration-bridge-20261024-laziness-caveat.md`, 2200bytes, SHA-256 `5092036015751e05b5c8ad5ac554c8fa463bff9ff43060a1cea4b25a6611d444`. The original codec proposal remains unchanged.

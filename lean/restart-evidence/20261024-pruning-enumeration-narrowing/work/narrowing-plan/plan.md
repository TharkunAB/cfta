# Computed narrowing and realized raw slots

Source-only plan. The companion freeze record gives the actual time and full source/cut hashes. No header, proof body, compiler, Git action, prepared program, or repository change is included. Root owns the current Writes bodies. Arity authored their declarations and this plan; this is not an independent reproof of that foundation.

## Smallest missing prerequisite

Add one codec inverse theorem, provisionally `lookup_encode`: for arbitrary full `Symbol`/`NativeGuard`, `Coherent heap` and ACTUAL `lookupNode heap handle = some value` imply `encodeNode value = some handle`. No Available, closedness, Ready, Constructed, output oracle, or DecidableEq premise is needed. The current codec exports forward available readback and growth preservation, but no inverse. The exact active codec and its entire current public inventory are pinned below.

This is not a definitional roundtrip on arbitrary heaps. A malformed positive record could carry an unrelated entry, Empty, or Reference. Coherent.nodes rules those cases out. This is why the theorem must retain a genuine coherence premise.

Proof route, not a proof body:

- Handle0: lookup forces `value = .empty`; its encoding is0.
- Handle `identity + 1`: split the actual issued-key lookup, canonical table lookup, winner identity test, and payload record lookup. Missing entries or a failed winner test contradict successful lookup.
- Apply `InternedRecordCoherence.Coherent.nodes` to the actual `nodeRecords key = some value`. It yields an entry, its table read, and `NodeFields key entry value`.
- Compare this table read with the SAME table read used by the decoder. Functionality of `Option` identifies the two complete entries. The decoder's winner test fixes their identity to the requested identity.
- Public `InternedRecordCoherence.fields_entry416–419` derives `entryOf value = some entry` from those fields. Cases on the value exclude Empty/Reference and identify the actual entry of Node/Union/Mu. Encoding is then precisely `identity + 1`.

Estimate45–75 total ordinary lines for this one public prerequisite, proposed hard90 subject to its future exact-header review. No helper or new definition is required. Existing `node_identity_unique` asks for Constructed and an Eq instance; those stronger premises are unnecessary. Existing `resident_identity_unique` is useful prior API, but the direct actual decoder/fields route is smaller here.

A separate general uniqueness theorem is NOT required for the later branch: two successful reads of the SAME lookup function at the SAME handle return the SAME complete value. `lookupNode_keeps` retains the old read in the final native heap. This elementary argument includes all constructor fields and does not identify payloads using an unproved reference-only law.

## Concrete narrowed-slot composition after that prerequisite

Inputs are one native `heap` with `Ready heap`, one enumeration `before`, `PendingRealized heap before`, actual raw read `before.values[slot]? = some (.unenumerated (some oldHandle) scs)`, and the existing `fits`, `admits`, `key` and EdgeKey Eq instance. Suspended constraints `scs` are arbitrary and retain their order. EnumGuard and NativeGuard remain distinct. No desired returned value, actual final certificate, assumed old encode equation, or arbitrary decoder is an input.

1. Apply incoming realization at this actual slot to derive `oldValue`, its actual `lookupNode heap oldHandle = some oldValue`, Available and literal closedness. Derive `encodeNode oldValue = some oldHandle` with the new inverse and `ready.semantic.1.normal.facts.coherent`. Do not substitute a handle merely supplied by a second forward readback.
2. Use `SourcePruningNativeView.narrowAt_complete60–79` on THIS old value and THIS heap. Derive finite actual `narrowAt ... oldValue heap = .done result nextHeap`, actual read/build steps, Keeps, available closed result, Ordinary, and the existing exact Empty law. No second execution supplies this result.
3. Obtain an actual computed `newHandle` and readback for `result` via `available_readback` in nextHeap. Its Coherent premise comes from `kept.ready.semantic.1.normal.facts.coherent`. Use `realized_preserved` with `Frame.refl before` and this actual Keeps to transport EVERY old pending slot to nextHeap. The native cache keeps all old lookups and available values.
4. Retain source branch order: if `result = .empty`, reject the enumeration branch before any identity comparison or write. Keep the actual native result/cache as evidence, but claim no successful final enumeration state for rejection. Do not add nonemptiness as a desired-result premise.
5. Otherwise compare the two computed model handles. In the equal branch, `lookupNode_keeps` retains oldValue's read at oldHandle in nextHeap. New readback at the equal handle identifies `result = oldValue` as a COMPLETE value. The enumeration action is `pure ()`, final enumeration state is EXACTLY before, and transported realization already holds. The actual native cache is still nextHeap; equal identity does not imply equal native heaps or absent constructor effects.
6. In the unequal branch, derive `slot < before.values.length` from the original actual slot read. Apply new `SourcePruningEnumerationWrites.write_available_realized41–67` to result in nextHeap, its derived Coherent/Available/closedness, transported realization and arbitrary original scs. Its existential written handle has the SAME result encoding as newHandle, so Option functionality identifies them. Retain actual setValue Success, exact full record update, exact new-slot readback, and final PendingRealized nextHeap. The operation writes the captured RAW slot; it does not silently find another representative.

The eventual theorem can expose both derived encode equations, the same actual narrowAt result/Keeps, and the Empty-rejected versus surviving branch packet. In a surviving branch, expose the literal action `if newHandle = oldHandle then pure () else setValue slot (.unenumerated (some newHandle) scs)`, actual Success, exact full final enumeration state and realization. The complete-value equality belongs in the equal-handle branch. No local extension/resource oracle is needed.

Estimate110–165 lines for this composition after the inverse is available, proposed hard180 only after exact declarations/inventories are reviewed. Do not combine both components under a smaller guessed cap. The immediate recommendation is the single codec inverse prerequisite, then the concrete composition.

## Identity and source-call boundaries

`cfta/src/Data/CFTA/Enumeration.hs981–990` tests Empty first, then compares native `nodeIdentity`, then resolves a representative only for a changed write. Native `Interned/Type.hs362–367` defines nodeIdentity for interned Node/Union/Mu and RecInt; it errors on Empty and unresolved cases. The adopted model convention is Empty0 and entry.identity+1. The inverse above establishes consistency INSIDE that model. It does not extract a native NodeId or prove Int/Nat/counter representation correspondence.

The native model already has `MergedSourceComparison.identity37–42`: Node/Union/Mu return entry.identity, an interned reference returns its ID, and Empty/other references return none. Available closed old values exclude all references. For a surviving narrowAt result, oldValue cannot be Empty: actual `MergedFreshOrdinaryExposure.nodeEdges37–48` reads Empty as empty rows with unchanged heap, and actual `makeNode248–253`/`run122–126` then return Empty unchanged at EVERY fuel. Derive this fact from the actual equation; do not require a supplied old-nonempty law. Thus identity is defined on both surviving complete values. Injectivity of the Nat shift then aligns their model handle comparison with this existing model numeric identity. Native NodeId extraction remains separate.

The actual Pruning.narrow caller has two bypasses: Mu alone, and incoming raw UVars at type positions. Those return the old value without invoking narrowAt. The concrete theorem above covers an actual call of the existing narrowAt helper, not that whole caller. Later caller composition must preserve its Mu-only/type-set tests; union is not exempt. The raw-slot theorem also starts AFTER the source representative is captured. An actual preceding representative success/frame can supply this state; no desired representative or equal forest is assumed here.

`EnumerationUntil106–124` currently accepts a PURE Nat narrowing function. It carries no native heap. An exact coupled native-heap result must therefore remain explicit in the consumer packet; do not claim whole-loop preservation or pass an unproved equality between that arbitrary function and the computed handle. Source memo2 realization, waiting/expandable cache fields, native laziness, errors, general intersection/assimilation, all metadata hole bounds and typedTypes end-to-end soundness remain separate.

## Preserved artifacts and live pins

The previous producer plan and frozen observation/Writes declaration owners remain unchanged. The companion record pins their exact controls plus all current source/cut references. There are no earlier drafts of this new plan, no mathematical correction, and no new compiler/public/Audit/seal/push claim. Public API absence refers to the complete current SourcePruningEnumerationNodes source, not a search over unrelated encoded models.

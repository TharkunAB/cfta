# Next native ordinary-edge operation: source assessment

Review cut: 2026-10-24 09:48 CEST. Status: SOURCE ASSESSMENT COMPLETE; CONCRETE CONSTRAINT PROJECTION AND DEFAULT EDGE ORDER REMAIN OPEN.

The next useful operation is the actual ordered ordinary-edge worker, rather than another theorem that packages child availability and closure. Its source behavior is `enumerateEdgeWith` in `cfta/src/Data/CFTA/Enumeration.hs:756–775`. It must consume one actual native edge, derive the complete ordered children from that edge, derive each child’s suspended constraints, prepare those children in order, and retain the residual obligation in the actual final enumeration state. This recommendation is conditional on the two prerequisites below. This report does not declare or implement that operation.

## Two prerequisites

**Concrete constraint projection.** The native worker first descends incoming constraints, rejects an inherited child index outside the actual arity, converts the selected edge’s actual equality classes with `pecToSuspendedConstraint`, descends those constraints into child buckets, then calls `prepareChild` in the order of `edgeChildren`. It finally appends the selected edge’s residual constraint and the actual returned fragment to `obligations` (`Enumeration.hs:756–775`). Native accessors retain the complete edge symbol, ordered children and constraint (`Interned/Type.hs:196–207`).

The current native heap model has a generic constraint field in its edge key. The enumeration `Edge` instead has ordered numeric children, a list of equality tries, and an optional residual guard (`EnumerationState.lean:36–49`). An opaque `NativeGuard` does not determine those equality tries, their suspended-variable actions, or the residual guard. A genuine specialization to the source constraint representation is required. An arbitrary projection callback, a desired worker-output equation, or an assumed Graph correspondence would leave this connection unproved. Existing child readback and allocation proofs do not supply it. The exact concrete carrier and its native encoding theorem remain to be selected; I have not inferred them from the generic field.

**Default edge order.** `Ord Edge` compares `edgeId` (`Interned/Type.hs:209–216`). Ordinary `nodeEdges` returns the stored `internedNodeEdges` (`Interned/Operations.hs:140–183`); ordinary construction uses a set of edge identities (`Interned/Type.hs:575–611`). The Lean `canonicalEdges` sorts and deduplicates edge identities (`InternedConstructorTemplates.lean:217–248`). These facts explain physical stored order.

Default enumeration instead uses `canonicalOrder` and `canonicalEdgesOf` (`Enumeration.hs:656–709`). Its key includes arity, symbol, canonical child classes, equalities and guard; optional weights can change the choice order. This is not edge-ID order. `runsInterned = runsFrom (const nodeEdges)` is an explicit alternative (`Enumeration.hs:1267–1274`). A selection action over the stored list would therefore model that physical-order route. It must not be presented as the default `termsPruneUntil` choice order. An individual-edge worker can avoid this selector question by retaining the actual selected edge as its input; a later selector must implement the chosen source ordering explicitly.

## Existing facts already close the record side

For a genuine available ordinary parent, `Available.children` yields availability of every member of the actual `edges.flatMap EdgeValue.children` (`InternedProbeProvenance.lean:14–52`). Coherence and the parent’s real residency establish its cached free-name equation (`InternedNormalizationFree.node_free`, lines17–23). Together with the parent’s closedness, `MergedColdReaderClosed.node_children_closed` (lines139–148) gives closure of those actual children. Merely asserting a malformed parent’s cached `free = []` without the real-record hypotheses is insufficient.

`InternedEdgeResidency.resident_edges` (line40 onward) uses `Linked` and actual parent residency to establish the selected edge’s complete stored payload. `SourcePruningEnumerationNodes.available_readback` then provides each child’s actual handle and complete payload readback; it does not replace the child by an independently chosen Graph node. The current `prepareChild_complete` uses these readbacks and the actual writes/allocations.

For the more general native exposure path, `MergedFreshOrdinaryColdEffects.Verified` already retains actual returned edge residency and child closure, and its `available` theorem transports availability to the actual returned heap. `MergedFreshOrdinaryColdTermination.read_closed` (line211 onward) already produces the actual finite read, final heap, edge and closure certificates, and retained read at larger fuel. Repackaging these certificates as another exposure theorem would not implement the missing enumeration operation.

## Smallest substantive component and coverage

After the concrete constraint specialization is available, implement the literal per-edge ordered preparation operation on the existing native `EdgeValue` and existing `EnumerateM`. Keep the original edge and its complete child list throughout. Compute the actual inherited/new child buckets, reject an invalid inherited position before child preparation, traverse children in source order, and append the actual residual obligation after the child fragment exists. Derive the native child availability/closure using the APIs above. Compose the existing allocation/write certificates at the actual successive enumeration states.

The current supported child action covers Empty rejection and nonterminal ordinary, retained-union and Mu children. Ordinary children retain the full suspended list in the fresh slot. Retained-union and Mu children allocate the source truncation slot with an empty suspended list. A closed available reference cannot occur. Terminal constraints still require the actual existing merge/eager path; that branch remains open and must not be defaulted to deferral. The existing child action also distinguishes unsupported/encoding absence from rejection. A nonterminal-only edge component must state this coverage explicitly and derive it from the computed buckets, rather than silently discard terminal buckets.

With reusable concrete constraint operations, an ordered child/preparation component and its actual-state certificate should take roughly 120–180 ordinary lines, with a proposed ceiling 220 before declaration review. This estimate excludes a new concrete constraint representation, proofs of its projection, the default canonical-order selector, and the terminal merge path. If those require new APIs, estimate them separately before selecting headers. The estimate is prospective, not an accepted cap or a claim that the prerequisites are proved.

No callback law, desired output, Graph equality, language preservation, full-driver correctness, native container extraction, machine-counter bound or pruning soundness is established here. The full goal remains ACTIVE. I did not author the native implementation, the current shallow-child body, or the exposure foundations. I reviewed the source and existing API route only. I ran no compiler, selected program, probe, import, Git, network or board operation and changed no repository file.

## Inspected input identities

Paths are relative to `/home/tritlo/Code/mcfta`. Hashes identify complete files. The assessment uses the bounded source locations stated above; it does not claim a new manual audit of every imported foundation.

| Path | Bytes | SHA-256 |
|---|---:|---|
| `cfta/src/Data/CFTA/Enumeration.hs` | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` |
| `cfta/src/Data/CFTA/Interned/Type.hs` | 36883 | `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77` |
| `cfta/src/Data/CFTA/Interned/Operations.hs` | 38260 | `1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836` |
| `lean/MicroCFTA/InternedConstructorTemplates.lean` | 46073 | `75aeb072ce0cfb7bc8bad40843184743281de8aeac1001c13ad941692d23e3f8` |
| `lean/MicroCFTA/InternedRecordCoherence.lean` | 26944 | `3f62016ee04aff34cc7902e7336f1bd879394aace92ff1a6db621670dd7d6d4f` |
| `lean/MicroCFTA/InternedProbeProvenance.lean` | 16949 | `9a0f3138d84df02b4aa36c754d7a19c995d2aacd120b5b35b190dfe0d7895ce1` |
| `lean/MicroCFTA/InternedEdgeResidency.lean` | 15975 | `c0596750df3bc2472271cf68451f233c27846bcff0baea5eb4d31da05d5723b0` |
| `lean/MicroCFTA/InternedNormalizationFree.lean` | 19564 | `947646cd523e5f1e776afef54db1f4a49e758c166852b3c298ebb1e621072891` |
| `lean/MicroCFTA/MergedColdReaderClosed.lean` | 16922 | `553007ae5c842332f5b9c42fe9168f6e4330ba7c0c1353050ced02052a720ce2` |
| `lean/MicroCFTA/MergedFreshOrdinaryColdEffects.lean` | 12822 | `ae73911d9897b289c96028b443ddaead58cfde91db633633dc4b4b879c054b05` |
| `lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean` | 18759 | `ab9083a8a5b8046651c920382118828ac1ca80ff1ca5cc55481a8ffe17362b47` |
| `lean/MicroCFTA/EnumerationState.lean` | 33489 | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` |
| `lean/MicroCFTA/SourcePruningEnumerationShallowChild.lean` | 6479 | `8210b17170fce05b31515e5f9b332799601fcfbc728263df6e2f53b917baed7c` |

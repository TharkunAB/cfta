# Concrete native node-view prerequisite for typedTypes

Recorded 2026-10-24 04:00:42 CEST. Read-only design. No declarations, proof body, compiler, prepared execution, or repository edit. This assessment reuses installed source APIs. It does not independently reprove their mathematical foundations. Root owns recordTypes and integration; required_memos owns its current pure helpers.

**Recommendation:** add a small Value-level native pruning view that calls the existing repaired public edge reader and actual makeNode. Do not change EnumerationState.Graph or accept a caller-supplied emptyAt function. Existing closure completion, live-row, normalization and cache-replay proofs already discharge most of this component. The remaining enumeration node-ID realization is separate and concrete.

## Native operation that must be retained

Pruning.hs127–141 exempts only native Mu from both narrowing and emptiness. A raw ID in the type-position set also bypasses narrow, but does not add a separate exemption to emptyAt. Type.hs matchMu771–784 recognizes only InternedMu. recursiveBoundary608–611 additionally recognizes InternedUnion; it is the renderer/scheduler boundary and cannot implement this test.

For every other node, expose native nodeEdges, keep exactly the source-selected existing edges, and apply the smart Node constructor. Source Ops161–182 returns ordinary rows directly; top-level Empty/Rec return []; direct Mu→ordinary uses its fast path; other Mu/union roots use an ID-visited closure, then canonical edge set conversion. A reference inside that closure is an error, not []. The observed root may be Empty; absence of a pending node is a different case and contributes false in typedTypes.

The source keeps predicate tests exact ordinary Top app/4 and filter/2 using admits on their annotation. Any remaining one-child edge uses admits plus fits on its complete symbol; every other edge is retained. Reuse full Symbol = SourceObservations.Label FullSyntax.Formula. Use EdgeValue.children for the actual annotation Value and retain the complete original edge symbol, constraint, child order and identity. Do not rebuild an edge or erase its refinement. Key, fits and admits are genuine existing public source parameters, not an invented emptiness oracle.

Type.hs543–586 shows that smart Node drops every edge with an Empty child before sorting/deduplication and interning. Checking only the raw filtered list is unsound for arbitrary edge payloads. On genuine closed reader output, the existing live-row theorem proves that extra removal has no effect; derive this fact rather than assume it.

## Exact existing APIs and what they establish

| API | Exact usable contract and scope |
|---|---|
| InternedConstructorTemplates.Value / EdgeValue (22–31), State (62–66) | Existing stored empty/reference/node/union/mu records, canonical entries, full row records and separate edge/node caches. No new node datatype is needed. |
| InternedEdgeResidency.nodeEdges (16–18) | Ordinary stored rows only; union/Mu/reference give []. It is not the Haskell public nodeEdges closure. Use it only for the ordinary result of makeNode or as the reader's constructor projection. |
| MergedFreshOrdinaryExposure.collect (18–34), nodeEdges (37–47) | Actual repaired worklist and unfolding with exact cache, direct fast paths, seen IDs and canonical fallback. Outcomes distinguish done, unresolved, pending and exhausted. The fuel is proof instrumentation. |
| MergedFreshOrdinaryColdTermination.read_closed (211–228) | With SemanticHeap, Covered [], InternedOpenDepthReadback.Heap, Available value and value.free=[], derives some finite fuel, rows and actual final cache; readiness components, resident closed rows, growth/history and stability at every larger bound. No preparation or supplied completion premise. |
| MergedFreshOrdinaryColdTermination.constructed_read_closed (231–245) | Derives all those premises and the read directly from an actual closed repaired build expression [] empty = done value state. No numeric bound oracle. |
| MergedFreshOrdinaryColdEffects.nodeEdges_verified (159–194) | Closed available reads from a semantic covered heap return resident closed rows on done; pending/unresolved are excluded; exhausted remains explicit at insufficient fuel. |
| MergedFreshOrdinaryExposureLive.nodeEdges_live (81–105) | Same SemanticHeap/Covered/Available/closed inputs derive no Empty child in every returned row. This justifies replacing smart-constructor empty-child filtering by the identity on genuine returned rows. |
| EqualityLeafProjectionPhysical.makeNode_edges (18–33) | Coherent+Linked cache and genuine resident input edges imply literal result rows = canonicalEdges(surviving inputs), including populated-cache hits. |
| InternedEmptyNormalization.makeNode_empty_iff (23–56) | Same cache/input premises imply actual returned reference is Empty iff every input row has an Empty child. reference_empty (19–20) relates this to the literal Value.empty constructor. |
| SourceEqualityRequiredCache.node (91–103) | Ready cache + resident closed rows derive Keeps, available returned Value, free=[] and Ordinary (empty or node). Ready18–22 packages precisely semantic, complete-payload and open-depth prerequisites. |
| MergedFreshOrdinaryColdReplay.nodeEdges_stable (229–246), nodeEdges_replay_stable (249–255) | Exact finished reader result/effects at larger fuel; any completed read replays identical rows without allocation in a growing valid later cache. Actual completion/growth remain explicit. |
| InternedNodeSetCongruence.makeNode_same_members (41–51), set_replay (80–88) | Equal surviving resident row membership gives equal complete constructor Work; after a real earlier request, a later equal set returns its exact record without allocation. Useful for cache extensionality; not a substitute for actual cache history. |
| SourceEqualityRequiredHead.Head/complete/unique (16–65) | Existing read-then-unfiltered-makeNode pattern proves finite completion and same returned Value/cache across successful read bounds. Reuse its proof route, but do not call this relation with filtered rows: Head.read requires its actual unfiltered reader output. |

These installed APIs genuinely cover closure, normalization and populated-cache behavior. General closed reader termination is already proved in ColdTermination; the older Exposure header/read_closed prepared-fragment discussion is not the strongest installed result. Stronger language/schedule correspondence is unnecessary for literal emptyAt. SourceRecursiveIntersectionScheduleConstructors.makeNode76–89 proves language correspondence to schedule syntax, not this enumeration node-view realization.

## Smallest additive model and next proof

Start with Value inputs and the existing constructor heap, not an arbitrary Nat decoder. Define a literal Mu-tag test by matching existing Value.mu, the concrete source keeps predicate, and a bounded narrowAt operation: existing repaired reader; propagate its actual failure/bound outcome; on done rows/middle, run makeNode(rows.filter keeps) in that SAME middle cache. Reuse MergedSourceComparison.Result for value/failure and final cache if a result carrier is needed. The Mu-only emptyAt wrapper returns false without reading/unfolding; other branches test the ordinary constructed result. A type-membership narrow wrapper returns the original Value without work in its two bypass cases.

The first useful theorem should be one closed, available non-Mu read/filter/construct producer. Premises: one Ready initial cache, Available initial value, closedness value.free=[], an explicit non-Mu constructor case, one concrete key and the actual source fits/admits functions. It derives finite reader fuel, its exact rows/middle cache, and the actual filtered makeNode result/final cache; the final result is available, closed and ordinary, and both cache histories and Ready are retained. It also derives the exact empty-result test: emptyAt is true iff no returned row satisfies keeps. There is no supplied final node, desired Boolean, row list, read-success or desired resource certificate premise.

Proof route: read_closed supplies actual rows, middle cache and resident/closed rows. nodeEdges_live supplies their live-child fact. Filtering preserves residence, closedness and liveness. SourceEqualityRequiredCache.node gives the actual result packet. makeNode_edges and makeNode_empty_iff reduce result emptiness to empty filtered rows; liveness then reduces that to no kept row. Handle Value.mu separately with literal unchanged/false equations, not with closure. This is a realistic approximately 90–140-line first module with the small executable wrappers and two or three composition lemmas; exact declarations and line budget need a fresh review before bodies.

For arbitrary partial/open stored values, keep unresolved/pending/exhausted outcomes visible. The closed completion theorem is a sufficient concrete scope, not an unconditional all-record guarantee. In particular, direct Rec returning [] does not justify swallowing an unresolved reference encountered inside a union. The decoder and native source must not default malformed/missing records to Empty.

The native memo2 wrapper (Memo.hs58–72) preserves the pure narrowAt kernel result and allocates its table for the source closure. It does not add fields to EnumerationState. The model can expose the concrete unmemoized computation; cache-hit/identity correspondence must use the actual constructor cache and replay laws above, not an assumption that any two independent cache histories have the same issued IDs.

## What remains before FULL typedTypes source correspondence

EnumerationState.Graph36–53 carries only empty/alternatives/recursive/unresolved on Nat identities. The installed EnumerationInternedRows.graph26–49 and EnumerationBuilderRuntime.graph265–285 realize ordinary row tables; neither carries the separate native union/Mu constructor tag or maps actual typed stored Value records to enumeration node IDs. MergedFreshOrdinaryGraph.graph27–29 instead has type EpsilonUnion.Graph(Value ...) Symbol. Its actual successors/Origin cover union/Mu reachability, but it is not a drop-in EnumerationState.Graph and does not prove the missing ID mapping.

Add a separate actual-record lookup/view beside the old graph. Compute a nonempty ordinary/union/Mu lookup from state.nodes.issued identity followed by state.nodeRecords key; prove the returned record's own reference/tag from Coherent and Covered. Use explicit empty/reference representations from existing NodeRef, with an explicitly reviewed Nat-ID encoding at the enumeration interface; do not silently reuse a raw integer for different tags. For each actual Some-node returned by the observer, its stored record/encoding and native-node interpretation must be proved from real construction/history. Mere arbitrary map agreement, desired final nodeEdges, or an emptyAt callback would assume the obligation.

The view must remain correlated with actual cache growth from closure and filtered construction. Native intern caches are distinct from the enumeration State; Frame alone has no native-heap field. Keep constructor-heap effects/cache-replay as a separate invariant and preserve the complete enumeration frame, including both ancestries and exact representative/root-size paths. No theorem here equates native global interning state with a compression-only frame.

Once that correspondence is available, typedTypes can compose existing getUnexpandedNode agreement/transport with the concrete node interpretation and emptyAt. Preserve ascending IntSet raw-ID order, read every hole before pure or, preserve aliases, and retain compression even when the callback returns earlier metadata after rejection. Current recordTypes is independent of this node-view prerequisite and need not wait for it.

## Live source pins and selected cuts

- `/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Pruning.hs`: 16989 B/350 lines; SHA256 `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61`.
  Cut 113–141: 1630 B, SHA256 `ed5c45adb6f5ad62e5e3ea0cfdec7ba23bdeb24f9b19e6a4fcba599a9cfee80a`.
- `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Type.hs`: 36883 B/922 lines; SHA256 `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77`.
  Cut 543–586: 1644 B, SHA256 `57f6619a28976cb8129232b3c355408234b9d8e5992d750af5de6086cb69c987`.
  Cut 608–611: 152 B, SHA256 `c36997b9cef53d6fc61f98f950a3d66d6ad4c4d62f94f81122c9093cd0655925`.
  Cut 671–675: 148 B, SHA256 `045b06616a1bedeadcc06f288327d42c360a81c5b26d1b27a4139df70d5d4eda`.
  Cut 767–784: 834 B, SHA256 `752aedd5a52f6c2aa95ef747da33b1097981403c43b046b2ae9d308577784c75`.
- `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Operations.hs`: 38260 B/887 lines; SHA256 `1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836`.
  Cut 144–182: 1767 B, SHA256 `f96bbc8074d51b690e76a8f84664048803795b01803e828032a33cd961cea06c`.
- `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Memo.hs`: 5024 B/128 lines; SHA256 `d96792d8007b9c925f7f524a36570f2d25b1496987b7aada043157c7d120ce58`.
  Cut 58–72: 582 B, SHA256 `254a029def1f42cab47bec28049e28e12d04c45f1b0aea33d0ea203ca5af04d2`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedConstructorTemplates.lean`: 46073 B/805 lines; SHA256 `75aeb072ce0cfb7bc8bad40843184743281de8aeac1001c13ad941692d23e3f8`.
  Cut 20–66: 2142 B, SHA256 `e0d17c88665bc3f3a67f0d10430729c880ad1b7c79a5429e0ce83d8c09974b98`.
  Cut 233–253: 1331 B, SHA256 `6ede20f36fa3a33a119c85ff892004641abec1c515e3ebc2fc6da493cfd7b91b`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedEdgeResidency.lean`: 15975 B/287 lines; SHA256 `c0596750df3bc2472271cf68451f233c27846bcff0baea5eb4d31da05d5723b0`.
  Cut 15–27: 639 B, SHA256 `9ff2f4a0158181eed2ce51e2e17d211a7a248ea4402c70deb18003460449d090`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/MergedFreshOrdinaryExposure.lean`: 10844 B/164 lines; SHA256 `76e836601211904253449e89df9f709075f508e58816104456489df3708a74e2`.
  Cut 17–47: 1766 B, SHA256 `94bd57065e1adef309c4bb07608d50ed4cba0422f63c3bbfa9cb1d43052a09fd`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean`: 18759 B/247 lines; SHA256 `ab9083a8a5b8046651c920382118828ac1ca80ff1ca5cc55481a8ffe17362b47`.
  Cut 200–245: 3989 B, SHA256 `06812e70d8812e994ebec1f3a42ad07b38df0bb8153f3c67ccb62b6ed7c870e9`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/MergedFreshOrdinaryColdEffects.lean`: 12822 B/196 lines; SHA256 `ae73911d9897b289c96028b443ddaead58cfde91db633633dc4b4b879c054b05`.
  Cut 23–33: 627 B, SHA256 `ea01a735a95782b3c7b46a4684dd9ffa518532eab610149404b7d37ec7700d3a`.
  Cut 158–194: 3098 B, SHA256 `6ad7a48d6d88b60b55b4397502b9e9dbc86921c839de10a61eb8658d7cf5f739`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/MergedFreshOrdinaryExposureLive.lean`: 7294 B/107 lines; SHA256 `c690b5e9bf78e1547795547f8bb9ff0b466dbde7fab0b4990c5b7d1593241ad8`.
  Cut 17–20: 227 B, SHA256 `3a5d72e7503cf890f0c74c7c0d047d8acef994a9c90e78aacc486398006ef521`.
  Cut 80–105: 2099 B, SHA256 `c38b66aa0ac47ddb5e35df61624ef8b4500497962712fa2fbc6d02499cfe0ba7`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EqualityLeafProjectionPhysical.lean`: 11366 B/177 lines; SHA256 `95c18033cc3fb94339a4198af7950c3f904c656a98870ffcf13736ef80201467`.
  Cut 17–51: 1985 B, SHA256 `33866e0008853fbc5093c42dd5b5de3a675378b5cbf305a6e61da39ef30bf9e0`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedEmptyNormalization.lean`: 8637 B/139 lines; SHA256 `1f18131da9693d23faa4ee55c05caeed0ac39972a691d703aa917039094ccf05`.
  Cut 18–56: 2116 B, SHA256 `d437f38bd622dc662c6dfeb7895c6b111fc128af89129b59eb53412017a1cdb0`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceEqualityRequiredCache.lean`: 6081 B/105 lines; SHA256 `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733`.
  Cut 18–28: 498 B, SHA256 `3c3e366b5087aef2b3f0e5c767ff7f1c5ce69af415c006eaeef77260c421bbb2`.
  Cut 67–103: 2164 B, SHA256 `038eaa24c0f854fe1594156393a57c6247feac3e44994c2902a642da8ee637bd`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/MergedFreshOrdinaryColdReplay.lean`: 17181 B/257 lines; SHA256 `534edc0c053b025623921f63c9d3fa0e874854561392055439925c3244eaba6f`.
  Cut 228–255: 1966 B, SHA256 `5a5e1ff66ac87e3e2d07d6e2d52e49c402b0ddbc35b62688633940c4a950beb0`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedNodeSetCongruence.lean`: 5157 B/90 lines; SHA256 `3e4effee1adb41eb8f606f52583f5bb2a1864f48ed42df75e06b4a3b097163ba`.
  Cut 40–51: 734 B, SHA256 `a80dd79bddc103b0866de07ee1f5c7a8f3d01dd0030e51f548039a84d1fd21e8`.
  Cut 79–88: 777 B, SHA256 `149e42d7eee59488c9c8cdb56f2facff1d41711276d2ac1a340cf15fd6a7b7cf`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceEqualityRequiredHead.lean`: 4929 B/77 lines; SHA256 `cc3f392f5545bea0abd678998e9d68bcb3e441269dd1715cabfd9370bb300013`.
  Cut 15–65: 3568 B, SHA256 `6a8db7fe3295d26c609654bc568db2b1656d1e8b37798e388a40cbab2b576d8b`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationState.lean`: 33489 B/699 lines; SHA256 `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.
  Cut 36–53: 653 B, SHA256 `f94dabb44627efc863f9fd14ee18a462abe7d92092dea58a1ab1cd9fdb182f82`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationInternedRows.lean`: 7727 B/138 lines; SHA256 `ec138999e1de79ff0e51afa61d6cfa35e663c7b7cbd54938535c5fc0e922324e`.
  Cut 15–49: 1881 B, SHA256 `ab38f6695a894ce98ac5d6c217f4efba0bb5735698c5004ef2205ee1417e2ee2`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationBuilderRuntime.lean`: 34864 B/559 lines; SHA256 `03857042a01483c406a7a941c6c082e9f897a8e07d8a0b3fab3fa91e21b86b98`.
  Cut 264–285: 1329 B, SHA256 `ae4169832d26f34d9279f6f00f2b7add8094916b50bd559a774c4973a66aee2a`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/MergedFreshOrdinaryGraph.lean`: 4336 B/81 lines; SHA256 `00d74646b29174976b2fb0b65dd0af4ae309deee31d35ac8591fed6e303f99a4`.
  Cut 16–34: 1104 B, SHA256 `47152183c5f1c24ae951c2e1f7f446580b8e1b035d43e8bc4e17c54ecef8a5bd`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceRecursiveIntersectionScheduleConstructors.lean`: 7225 B/112 lines; SHA256 `1533ff1d43e6c6943b127fe9c3cee5b5911dabea6722ea6c27cde51239bc3c1f`.
  Cut 75–89: 1085 B, SHA256 `9f484fbf44bddb82f15cacf1180e13f58dece32cb0ae36a8aee08c2e40a890f2`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedRecordCoherence.lean`: 26944 B/458 lines; SHA256 `3f62016ee04aff34cc7902e7336f1bd879394aace92ff1a6db621670dd7d6d4f`.
  Cut 17–42: 1696 B, SHA256 `2272b75ae060da2329d0799620b579fcff438f8e8137f8fdcafdc2f252c6a2a3`.

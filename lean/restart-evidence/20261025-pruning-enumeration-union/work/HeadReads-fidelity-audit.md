[2026-10-25 02:47:43 CEST] SOURCE-ONLY HeadReads proof-index fidelity audit.

Finding: the current frozen public contract does not tie its saved memo receipt to the internal bound of an independently selected Head proof. Head is a proposition. Proof irrelevance identifies its proofs at the same value/heap endpoints, even when their read constructors use different bounds. The words “same Head” must therefore identify those endpoints and the returned receipt, not equality of hidden bound witnesses.

The existing contract nevertheless entails a matching-bound existential packet. Eliminate the returned HeadReads receipt. Its sole read constructor exposes a Nat fuel, edges, middle, the actual nodeEdges equation, the actual makeNode equation and ExposureReads. Both the raw equation and ExposureReads use that same Nat fuel. They retain the public result, final heap, initial memos and saved memos. This is elimination from a proposition into an existential proposition; it does not require extracting executable data from a proof or using the originally selected Head's internal bound.

Therefore the minimal packet is sufficient for a later finite consumer that chooses this recovered bound. It is insufficient to identify that bound with another independently named Head bound, or to equate saved tables across increased bounds. Head.unique identifies only result/heap. exposure_unique assumes the same Nat fuel. The present theorem promises neither stronger property.

Recommendation: no logical strength repair is required for existential native Union composition. Returning explicit public fuel/edges/middle/raw equations/ExposureReads would make the correlation directly usable and reduce misleading prose. Root can select that interface before the body gate. It adds witnesses and a concrete case scope, not a new algorithm or assumed successful execution. Deriving the explicit packet from HeadReads would suffice; a second exposure_memos execution is unnecessary. If Root selects unchanged headers, later consumers must invert HeadReads and use its own recovered bound.

No owner, contract, mathematical body or instance changed. The129-payload frozen owner remains byte-exact. This audit does not claim a compiler result. No compiler, parser, reviewed program, Git, network, board or repository write ran. Guard independently confirmed the constructor argument on2026-10-25 at02:48CEST.

Exact personally read API identities (bytes and SHA-256; cuts inclusive):

| Source/cut | Whole bytes | Whole SHA-256 | Cut bytes | Cut SHA-256 |
| --- | ---: | --- | ---: | --- |
| lean/MicroCFTA/SourceEqualityRequiredHead.lean:16–20 | 4929 | `cc3f392f5545bea0abd678998e9d68bcb3e441269dd1715cabfd9370bb300013` | 417 | `d1fc69190a9ae51d4948e196ea834228f250c57f3d2055b68d57f82ff088676b` |
| lean/MicroCFTA/SourceCurrentRequiredQueryMemos.lean:24–33 | 23169 | `640a92bd071b92c629a007f8cc0d6501f0943de8deb605668e2e8cf4907e4fef` | 835 | `ad244e97b490362485d0495e714c604d0cd2264659cbc9626ac8dc0997dcf8bc` |
| lean/MicroCFTA/SourceEqualityQueryGlobalMemos.lean:25–50 | 5648 | `71333e9ca214137216850cf67f323608d8ded41ea596edb42be9a929ae727db6` | 1959 | `77e0dcf0e3e5e8a92ae870eae57daa55bc193b4d293ec48d979db00f3f78daa9` |
| lean/MicroCFTA/SourceCurrentAllocatedReadDeterminism.lean:37–43 | 4221 | `1dbd6e9f70d51782b470e8987388f7b3fb04ddb58129615b5cf778800482040e` | 547 | `9ce011c96f9033548106e7e860b8c46debc2ea4ed0a1e5de3af5e7a953a94ad3` |

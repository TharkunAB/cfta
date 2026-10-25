[2026-10-25 02:48:14 CEST] FINAL source-only Head receipt assessment.

The current existential packet is sufficient to recover a coupled bounded exposure receipt. It does not identify the fuel of an independently selected Head proof.

`Head` is a proposition (SourceEqualityRequiredHead:16–20). Its read constructor contains fuel, rows, an intermediate heap and the exposure/reconstruction equations. Proof irrelevance makes two Head proofs at the same value/heap endpoints equal. Therefore indexing `HeadReads` by that proof cannot certify equality with a separately named fuel. `Head.unique` fixes returned value and heap, not saved tables or fuel.

`HeadReads` has one constructor (SourceCurrentRequiredQueryMemos:25–33). Eliminating that receipt into a proposition exposes one fuel, rows and intermediate heap together with both raw equations and `ExposureReads` at that same fuel and the same incoming/returned memos. The indexed value/heap endpoints remain the public endpoints. This is existential witness recovery, not computational projection from a proposition and not cross-fuel memo equality. The current theorem can therefore support existential Union composition through receipt inversion.

For a consumer that must name the bounded exposure directly, return explicit existential fuel/rows/intermediate heap, both raw equations and Nat-indexed `ExposureReads`. This states the coupling without a proof-index convention. Existing `exposure_memos` (SourceEqualityQueryGlobalMemos:44–60) supplies a receipt at its explicit fuel. No new datatype, helper or successful-output premise is required. Root selects the interface before any body gate. This assessment does not authorize a body or claim compiler acceptance.

The original129-payload owner stays unchanged: FROZEN `7a313a6f939319bc9a4cbe604545d8d1d72ec1bec46e53329b5e78cf3dc1538d`; pins `72290c212e9008ff168621ff1ebfd307af63ad3b4b58c3541276cf0f68ac9ca6`. The earlier source review remains immutable. The current review read the complete Head module and the defining HeadReads/exposure_memos sections. No mathematical bodies, compiler, reviewed program, Git, network or repository edits were made.

| Whole source | SHA-256 |
| --- | --- |
| `lean/MicroCFTA/SourceEqualityRequiredHead.lean` | `cc3f392f5545bea0abd678998e9d68bcb3e441269dd1715cabfd9370bb300013` |
| `lean/MicroCFTA/SourceCurrentRequiredQueryMemos.lean` | `640a92bd071b92c629a007f8cc0d6501f0943de8deb605668e2e8cf4907e4fef` |
| `lean/MicroCFTA/SourceEqualityQueryGlobalMemos.lean` | `71333e9ca214137216850cf67f323608d8ded41ea596edb42be9a929ae727db6` |

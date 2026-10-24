# Independent stored-node handle declaration review

[2026-10-24 04:58:33 CEST] CLEAR for the exact declaration proposal. This is not a body review, compiler result or native NodeId extraction theorem. Arity authored the proposal. Root retains separate body/compilation authority. I performed source/API and frozen-package checks only; no compiler, selected program, Git, repository mutation or board operation ran.

I read all five STRING fragments (16 compiled lines), their complete combined review file, operation-contracts, full scoped type/case/equation inventory, schema, proof route, insertion map and self-review. The combined file is exactly those fragments in order with blank separators and namespace end. There are exactly two computed definitions encodeNode/lookupNode and two theorems available_readback/lookupNode_keeps. No helper, new type, abbreviation, local/global instance, axiom, recursive call or IH is proposed. The75–115 target/hard140 is realistic for this nonrecursive scope; shorter source requires no padding.

encodeNode uses full existing Value constructors. Empty is some0; Reference is none; stored node/union/Mu use their canonical entry.identity+1. lookupNode0 returns actual Empty. A positive handle reads issued identity, then the actual canonical table entry for that key, compares that entry's identity with the requested identity, and only then reads the complete node record. Every missing step, pending payload or losing reserved identity returns none. There is no default Empty, issued-only decoder or caller-supplied decode result. Only Nat equality is required; no Symbol/Guard/EdgeKey equality instance is added.

The winner check is essential. A losing candidate can be issued for a key whose installed entry has another identity. An issued-key-only reader would incorrectly give the winner's payload for that losing handle. The proposed check rejects this case even when the payload exists. This is a distinction in the existing reservation/cache model, not a reported native defect.

available_readback has sufficient genuine inputs and no desired readback premise. For node/union/Mu, Available.resident yields the actual complete stored payload. resident_entry with Coherent derives the exact canonical entry. The node-cache Valid component of Coherent derives its issued key. The equality check then accepts that same identity and the final record lookup returns the SAME full Value, preserving refinements, guards, children and stored metadata. Closedness excludes Reference because its free list is [name]; Empty has the literal zero witness. No Ready, dense table, source counter bound, constructed-run certificate or arbitrary node witness is required.

lookupNode_keeps assumes an ACTUAL successful BEFORE lookup and the existing actual Keeps packet. Its zero branch is unchanged. In the positive branch, named issued/canonical Option equations and the winner equality expose the successful original payload. kept.history preserves issued, kept.growth.nodes preserves the canonical entry, and kept.growth.nodeRecords preserves the exact record. These derive the successful AFTER lookup; no final lookup or new replay assumption is supplied. The invariant applies to the actual returned heaps, not a reset/fresh replacement heap. All declared constructor fields, two scoped canonical/issued haves and four Option-equation specializations match their source types.

I read every retained primary cut:14 cuts/268 lines across10 sources. I supplemented the cut ending inside Cache.Valid with its complete definition at Cache136–140, the Grows definition through all four table fields at InternedConstructorTemplates77–83, and Value.free45–52 to check the Reference contradiction. All10 full snapshots and every cut are live-byte identical; full snapshots were hashed, not all manually read. All nine static import routes have their actual import-text edges. These are source checks, not elaboration evidence.

The0/positive-ID+1 convention is already used by EnumerationBuilderCaches.rows103–106. The new strict Option decoder does NOT claim that older getD/issued-based rows implementation has the same rejection behavior. Native nodeIdentity is partial on Empty and has a different raw NodeId interface; no identity conversion theorem is inferred. Raw UVar IDs remain separate. Graph correlation, initial enumeration-slot realization and its preservation through actual slot writes are future consumers. The separately retained laziness caveat leaves native observation traversal versus demanded constructor-call history open; these pure handle declarations do not resolve or assume that correspondence.

Frozen validation passed using read-only Python: exactly41 safe relative object-pin entries, each with bytes/SHA256, equal the complete recursive payload file set. ONLY top-level pins.json and FROZEN.json are excluded. No symlink or unsafe relative path is accepted. All five contract hashes/order, all source/cut identities, nine static routes and the three provenance reference byte/hash pairs match. I read the laziness caveat; the larger prior-plan reference was verified by bytes/hash without a new whole-plan review. The original native-view proposal and earlier checkpoints remain unchanged.

Exact input pins (SHA256):

- FROZEN.json: 584 bytes,bb31c6deda8dfa33d6a42def286612a703ffec6875427b0a87b24969966c9c7b.
- pins.json: 5591 bytes,28de6f4f508a43e7842670f07b97eb6114e65611471012f48d0ea1937ecbefa5.
- contracts.json: 507 bytes,9a934ab7e005abb4be6cb2387500b588c90be95da9c2d33c7ac449fa78f0b6c8.
- declarations-review.lean.txt: 967 bytes,a2c92d37b00f9ef4e7d42fb050f37d499f0e1ef95eb9aa69c3efb54f5283a548.
- context.lean.txt: 231 bytes,cc39e711f8f0575d39aae3c1b895213e3a7004f46d24f769c49e01738e2df498.
- encodeNode-header.lean.txt: 57 bytes,b955bd4ffb0ca6aa0dfb80ca90e436b633e139e19dda76e12e6bdcce59f8f30e.
- lookupNode-header.lean.txt: 86 bytes,937272071c95fd9ee09637302c3710e1837a6beffe3dd6cd94634e8c090a4a3d.
- available-readback-header.lean.txt: 288 bytes,91b628bcef9a98542781613467116d85502c1302045c7f297844c9981fdaf0ae.
- lookupNode-keeps-header.lean.txt: 256 bytes,cbf2e798a48f7056878ef4df3a0b57d7231bbf34d2a63342676d4c99db45f8c0.
- operation-contracts.json: 1694 bytes,17c8c6aa8c43d3028eb700baec9af8b5898da622afcc99f5f8f1f8eb47a4b9f6.
- scoped-types.json: 6106 bytes,a9eaf95c1daf88ce989abc7452814ddccf2ce403b866598f191bc81af1aadf1b.
- source-index.json: 10379 bytes,73d494c623905b6fc25ebbc413b223da9e015fc98e70ee7699f6e9aacdc8555c.

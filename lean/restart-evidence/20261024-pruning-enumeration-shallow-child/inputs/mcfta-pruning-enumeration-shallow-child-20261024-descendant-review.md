# Recursive shallow-child descendant constraints

Status: SOURCE_DERIVED_TRUNCATION_BEHAVIOR; NO_NATIVE_BUG_ESTABLISHED.
Reviewed 2026-10-24 at09:13 CEST. This is an independent bounded source audit. I ran no Haskell/Lean/compiler/parser, candidate program/import, Git/network/board action or repository write. Only this requested report is created. Fresh usage read at09:09 showed87% remaining and sample age15s.

The no-terminal Mu/InternedUnion branch does discard a concrete suspended path-equality requirement. That loss is not a proof that the native source is wrong: the current public contract expressly permits it at a truncation boundary. Enumeration.hs1205–1207 says: "A constraint whose paths descend into a truncated recursive binder is dropped rather than checked" and warns that a marker-containing result does not establish nonempty language below it. The actual recursiveBoundary definition at Interned/Type.hs608–611 includes BOTH InternedMu and InternedUnion. It is not restricted to the Mu pattern used by the pruning type exemption.

Actual effects are unambiguous. Enumeration.hs718 partitions scs into terminal and descendant obligations. With no terminal endpoint, lines721–722 call addUVarValue(Just n) for Mu/InternedUnion and do not pass descendantConstraints. addUVarValue at389–403 constructs UVarUnenumerated x Sequence.Empty; it also updates candidates and ancestry. The new slot therefore has no waiting references from the discarded obligations. expandable at472–474 returns false for this recursive-boundary/empty-scs slot. expandPartialTermFrag at1041–1046 reports TruncatedRecursion, not a pending UVarHole. The complete diagnostic renderer at1050–1074 likewise returns its supplied recursion marker.

In contrast, prepareShallowChild796–800 allocates an ordinary Node child and then explicitly setUVarValue with the FULL original scs, including descendant obligations and their waiting counts. With a terminal endpoint it falls back to enumerateNode, whose terminal branch730–747 merges the reached equality classes and installs descendantConstraints. enumerateShallowHere783–787 uses the supplied child preparation only for an ordinary selected root with no terminal endpoint. The fallback at801 deliberately preserves the existing Mu/Union allocation behavior. Merely proving that every fallback preserves the incoming scs would contradict the source.

## Minimal source-level witness

Use distinct symbols p,u,v,a,b. Let a and b each denote their separate nullary ordinary node. Let R be Mu self with two ordinary alternatives u[a] and v[self]. The binder is genuine: self occurs below v, so createMu688–700 does not erase it. R accepts exactly v^k(u(a)) for k≥0, so R is nonempty. Its internal edges carry no equality constraints.

Give a root p[R,b] the one equality class containing paths[0,0] and[1]. These are different, neither is a prefix of the other, and both first indices fit the root's two children. The mkEdge548–568 checks do not compare their selected languages; this class is not a syntactic path contradiction. No finite concrete completion satisfies it: path[1] is b, but path[0,0] in any R term is either a or another term rooted at u/v, never b.

Source trace, not an executed reproducer:

1. enumerateEdge creates one pure equality UVar q for that class and descends the trie into each child (Enumeration.hs480–483 and760–770).
2. The R child receives the proper descendant obligation for remaining path[0] pointing to q. It has no terminal path. prepareShallowChild falls back to enumerateNode; the Mu branch allocates a separate fresh slot r containing R with EMPTY scs. It returns TermFragmentUVar r. There is no merge r=q and no pending reference to q in r.
3. The b child receives a terminal obligation pointing to q. Its fallback merges/stores b in q through the existing terminal path; there are no remaining descendant constraints. In the initialized default run q was a pure constraint slot, so this is not a conflicting b/R intersection.
4. Slot r is a noncandidate recursive boundary with empty scs. Slot q can enumerate the nullary b. The diagnostic fragment can therefore render p[TruncatedRecursion,b]. Under terms/runs the corresponding display uses the caller's recursion marker. The same local loss occurs under shallow preparation with no pruning/stopping intervention.

This is a concrete witness that the equality obligation is discarded and that the marked result need not have a valid completion. It is not a source-level witness of an INVALID UNMARKED concrete output, and I did not execute it or claim a reproduced native failure. The public truncation warning predicts precisely this distinction. The existing tests EqualitySpec.hs718–737 explicitly expect bare/nested Mu truncation and repeated-recursion marker results; the623–630 test concerns explicit constraint reduction/unrolling, not a theorem that enumeration preserves all descendant equalities across a marker.

## Union and proof boundaries

createUnion at Interned/Type.hs592–605 collapses a union of ordinary nodes to ordinary edges. Thus one must not use an ordinary union expression as an alleged witness of the InternedUnion branch. A retained union can include recursive/open operands; the source explicitly classifies the actual InternedUnion constructor as a diagnostic recursive boundary. nodeEdges can expose its alternatives later (Operations.hs160–183), and enumerateOutUVarWith895–898 does so when that slot actually has work. None of that restores obligations already dropped by the no-terminal fresh allocation. This audit does not claim that every union has a recursive language, or that open reference resolution is complete. The exact native constructor classification, not a Mu-only assumption, belongs in a source-fidelity proof.

The Lean action model mirrors the same local behavior. EnumerationState.lean201–225 allocates a .recursive view with no scs when no terminal is present. EnumerationUntil.lean42–54 writes full scs only for an ordinary alternatives view; all other views use enumerateNode. Its native Mu/Union Graph correspondence remains a separate obligation. Suspended.Holds at EnumerationState.lean27–28 requires the assigned common subtree at EVERY represented path. For the witness, assigning q=b and the recursive result u(a) does not satisfy the incoming[0] obligation. One cannot silently extend unconditional suspended-assignment preservation to this cutoff branch.

Existing language soundness avoids that claim: EnumerationSemantics.lean382–385 defines CompleteGraph to exclude every .recursive view. EnumerationSoundness.enumerateFully_backward at83–89 explicitly requires CompleteGraph; EnumerationLanguage accepted_iff/runs_uniform_height_bound likewise retain that premise. Their conclusions do not certify marked recursive diagnostic output. A next shallow-child operational proof can state the actual fresh empty-scs effect for Mu/Union and the full-scs ordinary effect. Stronger equality/language claims must either exclude this cutoff, expose marker/truncation semantics, or separately prove a suitable property. Cache/waiting correctness should count the ACTUALLY stored empty list; it must not invent discarded references.

No repair is recommended from this audit alone. No entire renderer, complete source pipeline, native acceptance theorem or runtime experiment was proved here. Full source files were hashed programmatically; I read the relevant ordinary source/API cuts and existing targeted tests, not every large source or historical proof.

## Exact input identities

Paths are relative to /home/tritlo/Code/mcfta. Hashes identify the complete live files at this source cut.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| cfta/src/Data/CFTA/Enumeration.hs | 71269 | 949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07 |
| cfta/src/Data/CFTA/Interned/Type.hs | 36883 | f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77 |
| cfta/src/Data/CFTA/Interned/Operations.hs | 38260 | 1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836 |
| cfta/src/Data/CFTA/Equality/Constraint.hs | 21706 | 9dd1a13bd4422a0778bee419679f34e45901ec1d38442a46781df84952537c48 |
| cfta/test/Data/CFTA/EqualitySpec.hs | 96780 | e23cf22ec784f6b589afbff1b9be381864cc8b0a4665fc98290f1dd480413ed6 |
| lean/MicroCFTA/EnumerationState.lean | 33489 | 83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4 |
| lean/MicroCFTA/EnumerationUntil.lean | 8864 | 3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137 |
| lean/MicroCFTA/EnumerationSemantics.lean | 42969 | 69ef14d4cfe44c8d448b5ea1a0521526f654caabd6e12b126463344733ad3a62 |
| lean/MicroCFTA/EnumerationSoundness.lean | 17374 | 91b737c2e21a2d39cfb31b9a8cf6d27472d91c74e07ea68b71516e37d29ee27b |
| lean/MicroCFTA/EnumerationLanguage.lean | 7440 | 02e092308a26e60e9e493a1a30ae3a5e2bb17ecd41b819d2ca12b82f2f6f3886 |
| lean/MicroCFTA/EnumerationCorrectness.lean | 76898 | 087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d |

Key exact LF-preserving line slices:

| File and lines | Bytes | SHA-256 |
| --- | ---: | --- |
| cfta/src/Data/CFTA/Enumeration.hs:711–801 | 4694 | b39491a97e8ae7f1b2993b2b91674f65d0e56c64806ca55b2bfcbca9a5d1f899 |
| cfta/src/Data/CFTA/Enumeration.hs:383–410 | 890 | 2290cf8ab5faa147fef4784f88f31a82cf5cf6c5470f189ee8c200827a913d91 |
| cfta/src/Data/CFTA/Enumeration.hs:444–483 | 1672 | a3b9ca2db75598db143cf6906038c496ec2ab7ce7f5a14ddead12740f9e0b422 |
| cfta/src/Data/CFTA/Enumeration.hs:1029–1075 | 2451 | 317d830f5aa2fc2b8bc4612313deff4b9073db2ff0649cdf875e530523f1b610 |
| cfta/src/Data/CFTA/Enumeration.hs:1167–1207 | 2161 | 49821b4d9d5358225a14a214f021f1843ac5fad6557e50fee099b98e24c3653e |
| cfta/src/Data/CFTA/Interned/Type.hs:575–611 | 1440 | a6ab4afa53a01e1ceaf9a3e9af4c94cf64d95e1257c1f862f41ee67a95be6b5c |
| lean/MicroCFTA/EnumerationUntil.lean:20–66 | 2190 | 5bb5fa182458504a202cc016f28a6ff4ea8a58179f5f0477c58533fb846b23f5 |
| lean/MicroCFTA/EnumerationSemantics.lean:375–391 | 1122 | 035273b9f80a8b7e1356f894ce99f75aed19fa9a0594a71e98432a8aab6a6447 |

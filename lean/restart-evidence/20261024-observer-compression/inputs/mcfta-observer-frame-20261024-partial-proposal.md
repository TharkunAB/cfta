# Partial-render observation under the complete compression frame

Source-only proposal, 2026-10-24T02:11:49+02:00. HEAD ae8970309774ea10a833b64de7945f48d50ff11e. No candidate code, compiler, selected program, repository edit, Git mutation, network or board operation.

The exact current action is EnumerationState.expandPartial graph fuel fragment (State.lean342–356). EnumerationUntil.partialRunsUntil calls it directly after rootFragment. The Haskell public expandPartialTermFrag is Enumeration.hs1038–1046. Both preserve symbol and child order, follow an enumerated slot, emit truncation only for a recursive boundary with EMPTY suspended constraints, and emit the ORIGINAL queried UVar ID for other pending/eliminated slots. A recursive node with pending constraints stays a hole. Haskell recursiveBoundary includes InternedMu and InternedUnion; the graph interpretation must retain both as the model's recursive view. A missing stored slot can still fail its getValue read.

A repository-wide search found no existing expandPartial theorem family, apart from the executable example in EnumerationState.lean659. Existing expandFragment proofs concern concrete completed rendering, so they are proof patterns rather than partial-render semantics. Do not replace expandPartial with expandFragment or Fragments.fill: the marker and pending-hole branches differ.

Recommended first statement (all variables explicit; notation abbreviates the existing actions): for any graph, fragment, before, peer, afterA, afterB, termA, termB, fuelA and fuelB,

    Frame before peer → UnionFind.Total before.representatives →
    Success (expandPartial graph fuelA fragment) before termA afterA →
    Success (expandPartial graph fuelB fragment) peer termB afterB →
    termA = termB ∧ Frame afterA afterB.

The two bounds are independent. Prove preservation as a reusable local fact: Total before.representatives plus one successful expandPartial render implies Frame before after. Total is the weakest ready-made premise needed by the EXISTING getValue_frame/findRoot_reaches_iff APIs. It does not require Safe, Finished, graph completeness, an accepted assignment, hole bounds, or a success/counter oracle. Removing Total would require strengthening the union-find reflection API and is unnecessary for callers that already supply actual root paths.

Recommended existence statement, using the SAME supplied fragment and observed successful render:

    Frame before peer → UnionFind.Total before.representatives →
    Success (expandPartial graph fuel fragment) before term after →
    ∃ peerFuel peerAfter,
      Success (expandPartial graph peerFuel fragment) peer term peerAfter ∧
      Frame before after ∧ Frame peer peerAfter ∧ Frame after peerAfter.

This is transport of an actual successful observation, not unconditional termination. Total forests alone do not make a partial render terminate: a root slot holding enumerated(.hole root) recursively unfolds forever. Existing EnumerationRendering.expandFragment_complete uses Safe/Finished/provenance/stratification for a different completed renderer; it cannot discharge this arbitrary partial case.

Proof route, with existing definitions and no observer DSL:

1. Reuse getValue_success, UnionFind.findRoot_correct/reaches_unique/findRoot_terminates, and Frame.values/reaches. Two observed reads return the same root slot. One observed read supplies a path and stored payload in peer; a finite peer lookup follows. Reuse getValue_frame and Frame.total for complete post-read frames. A small Frame.symm fact, plus existing Frame.trans, relates the actual post-read states.
2. Prove expandPartial frame preservation by induction on its existing fuel. The node branch composes child frames with mapM_invariant; the hole branch uses getValue_frame, then the induction hypothesis only for an enumerated payload. Terminal branches are pure. Both ancestry fields remain present.
3. Prove observed-output equality by induction on the first successful bound, generalizing the second bound and states. Decompose both actions with success_bind/success_pure and List.mapM_cons. Use a local ordered-list induction for children. Related reads choose identical value/graph/scs branches. Raw hole IDs remain equal because the input fragment is identical; do not rename holes to representatives.
4. For the existential counterpart, add expandPartial_moreFuel as the direct partial analogue of EnumerationExecution.expandFragment_moreFuel. It reuses getValue_moreFuel, retains_bind and retains_mapM. Induct on the observed successful source render. Transfer each read to a finite peer bound; combine finitely many child/read bounds by sums or maxima and raise them with Retains. Preserve the actual peer intermediate states and child order. No new state or semantic relation is needed.

Minimal imports: EnumerationCompressionFrame and EnumerationExecution. The concrete Rendering/Driver proofs are source references only. No new dependency on the completed-rendering invariant pipeline is required. Once the fragment theorem is checked, rootFragment can be handled separately with the same value-read lemma; arbitrary user oracles still need their own congruence premise. ReadOnlyOracle alone is insufficient.

Concrete equal-fuel obstruction: before has parent chain 0→1→2 and root2, while peer has 0→2 and 1→2 with the same root size and all other fields. They satisfy Frame. With slot2 pending and fragment .hole0, expandPartial at bound2 can finish in peer but the original lookup needs bound3. Therefore neither equal-fuel action equality nor a same-bound success transfer follows from Frame.

Scope: exact modeled output identity and the complete final State frame, not equal forests, arbitrary callback identity, full driver equivalence, native container realization, accepted completion, or resource bounds. Read the complete Haskell function and exact Lean partial definition; supporting API reads are the bounded cuts below. No whole-library read is claimed.

Source identities (UTF-8 bytes; cut hashes include original line endings):

| Source | Full bytes | Full SHA256 | Cuts: lines, bytes, SHA256 |
| --- | ---: | --- | --- |
| `cfta/src/Data/CFTA/Enumeration.hs` | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 1018–1026, 243, `ab5a1d7157cf7731a0b63b3d3c8bde59da04bca5bb67d781c9873ac335ad9122`<br>1028–1046, 1130, `d33fd1f245bb758a4babf2b511f6b17283c348d207a6391a904419cc827e5c86` |
| `cfta/src/Data/CFTA/Interned/Type.hs` | 36883 | `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77` | 608–611, 152, `c36997b9cef53d6fc61f98f950a3d66d6ad4c4d62f94f81122c9093cd0655925` |
| `lean/MicroCFTA/EnumerationState.lean` | 33489 | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 335–356, 1011, `ebbb63942b8f89846f6d258bf30a6f13a32d9a1689b5687ed5aad69f59dce2e5`<br>358–374, 814, `6e6cc56715dc80a2d443a3e87b735eeaf7ab7c4ee093c9a47bc4165da4311367` |
| `lean/MicroCFTA/EnumerationUntil.lean` | 8864 | `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137` | 134–152, 1157, `18b0660b5ce866e703566889c49159b0b2537781744ab34305976db948593088` |
| `lean/MicroCFTA/EnumerationCompressionFrame.lean` | 8220 | `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375` | 20–87, 3883, `30450514a7b8dcdce2d372b24daaa70b9d344b97ecff794b8dd4409540d1fa1b` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 76898 | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 37–40, 196, `85a7d471fb36781cf644c270d0f1ff74b29558aaf2991b6d02fa603d629e9c3a`<br>55–67, 820, `43ce2dce60f56fa055f88b8e5e441272586a38ff9270a60639811b1f345325bc`<br>1007–1032, 1883, `569a23e0ed0554002228945c61451395c371bfa6de6ce05a3d9215e6d2b99eda`<br>1071–1100, 1775, `e056b566425eafa6e66f8a9552a93ea180cf5219d667110515afcb3b8a393ec5` |
| `lean/MicroCFTA/EnumerationSchedule.lean` | 86287 | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` | 1062–1081, 1378, `9f01ea57d504ed3be5876d4a9138cb4101f6445ca6e310b411ccf8568c0b38ed` |
| `lean/MicroCFTA/EnumerationDriver.lean` | 52410 | `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf` | 664–691, 1954, `d3bdecb1a0c553f1b4cd868175ee6c4b12e87c1ef2e56ffb70d15cb3aa7bb823`<br>704–753, 3398, `5fbe09ec2fc294360d878f6b346442ac555ce31d341359dc0f4fe593080532c1` |
| `lean/MicroCFTA/EnumerationExecution.lean` | 30176 | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` | 35–63, 1549, `b1ee35731793270c8c3bdc1617dda608d2a4c173d08036cb917e38ddbf2263ca`<br>95–110, 1100, `0a8ebac94442add5e895c26acb37c5c48c866c8e4292a067c5b8890296eec8bc`<br>290–311, 1074, `20aaffbf68be3693e9950939e94beff685c980b96a3426b79fe88e0f30db1c30` |
| `lean/MicroCFTA/EnumerationRendering.lean` | 13057 | `be611f9aa9e285872251ad14a40126fa358f393520f14576c9770ffa959db1a9` | 37–68, 2834, `9c118f33d17d1166e71e8c92394f494185ce4f5ffa2872c734c0004652bf8a74`<br>70–128, 4804, `f6ac949799d2edf104651616421c063d4f3f43828ec0be15b255da42777b476f` |
| `lean/MicroCFTA/UnionFind.lean` | 41077 | `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14` | 107–170, 2920, `5ba71ce2d93f793cfc6dfd58d11a8126708ad4ffb8b46e54c5064edd60f8dd6f`<br>201–221, 1065, `538bc0b5f0151702ed1e933a9eb1eca1cd29ae12537abfc2d396f63ce19cfa58` |

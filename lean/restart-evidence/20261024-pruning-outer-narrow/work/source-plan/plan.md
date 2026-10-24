# Outer pruning narrow: smallest concrete wrapper

Source-only assessment at 2026-10-24 07:02:16 CEST. No declaration, mathematical body, compiler, prepared program, repository/Git/network action or board action is included. The current narrowing owner remains unchanged. Arity authored that declaration design and this assessment; Root owns mathematical bodies. This is a new control-flow assessment, not independent reproof of that design.

The smallest useful next component is one Value-level wrapper over the EXISTING SourcePruningRecordTypes.Metadata Typing and existing MergedSourceComparison.Result carrier. It needs no new metadata, graph, state, predicate or callback framework. Its two bypasses return the complete original Value and the same native heap. Only its fallback invokes the actual NativeView.narrowAt. This isolates the literal Pruning.hs127–132 decision without duplicating the pending-read/write packet.

## Concrete inputs and output

Use the fixed complete SourcePruningTemplates.Symbol, arbitrary NativeGuard, Typing and Key, the existing native EdgeKey equality instance, metadata : SourcePruningRecordTypes.Metadata Typing, the ORIGINAL selected raw uv : Nat, an interned complete Value, its native heap and a native fuel. Keep the source public parameters holeKey : Typing → Nat → Key, fits : Key → Symbol → Bool and admits : Key → Value Symbol NativeGuard → Bool. Return the existing MergedSourceComparison.Result Symbol NativeGuard (Value Symbol NativeGuard), including every actual failure heap from a delegated narrowAt. The wrapper itself does not need EnumGuard or an enumeration state; later coupling keeps EnumGuard and NativeGuard independent.

The exact proposed control order is: inspect the actual Value constructor; Mu returns .done original heap. For every other constructor, test membership of the original uv in metadata.types; a member returns .done original heap. Otherwise call existing narrowAt fits admits fuel (holeKey metadata.typing uv) original heap. Do not evaluate a representative, substitute its root for uv, use updatedTypes, or replace metadata.typing with a supplied replacement typing. Do not compute a key for the bypass branches.

Native Mu is a pattern synonym backed by matchMu, which returns Just only on InternedMu. Thus the corresponding Value.mu test is Mu-only. Native recursiveBoundary also accepts InternedUnion and is the WRONG test here. A non-type union takes the narrowing fallback and its actual repaired row exposure. Empty/reference cases retain the literal same branch selection; availability/closedness for finite completion is a separate theorem premise, not part of the wrapper definition.

## Minimum public proof packet

1. An all-fuel Mu equation: exact original complete Mu Value and identical heap, including fuel0. It needs no Ready, Available, closedness or desired result premise. It invokes no holeKey, reader, constructor or memo operation.
2. A raw-type-membership equation: when metadata.types contains the original uv, return the original complete Value and identical heap at every fuel. This is valid for all Value shapes; the implementation must still inspect Mu first. The wrapper changes none of pending/types/openHoles/typing. List membership needs no sortedness or uniqueness assumption. Those are separate native IntSet representation requirements.
3. A non-Mu/non-type equation: the wrapper is exactly the SAME narrowAt call at holeKey metadata.typing uv, with the actual returned state and all failure cases. This is an equation of actual definitions, not an assumed callback/output law.
4. If useful in the same bounded module, finite completion under Ready heap plus Available heap original and original.free=[]: bypasses use the exact no-effect equations and pure_keeps; fallback uses narrowAt_complete once. Return its actual result/nextHeap, Keeps, availability/closedness and chosen-run larger-fuel retention. No Ready or resource certificate is assumed for the final heap. Both bypasses retain original fields; do not assert Ordinary for the combined result because a Mu bypass returns Mu.

One definition plus these three branch equations should take about35–60 ordinary lines. Adding the small finite producer should fit about70–115 lines, proposed hard140 only after exact declaration review. These are scope estimates, not a new header/body authorization. No helper, local monad instance, recursive proof or new type is needed for this Value-level wrapper.

“No work” here means no modeled native heap operation in the bypass. It is not a runtime allocation, memory or timing assertion. A bypass does not invoke memo2; fallback still has the native memo2 correspondence boundary. In particular, an equal returned model handle after actual fallback does not imply that its actual nextHeap equals the initial heap.

## Reuse and later enumeration coupling

Imports can be just SourcePruningRecordTypes, SourcePruningNativeView and, if finite no-effect preservation is stated, its already imported SourceEqualityRequiredCache. Metadata already exposes raw types and typing. NativeView supplies the actual repaired narrowAt and finite run/retention. Ready→Coherent and Keeps→final Ready are already available. SourcePruningPositions and Templates provide the existing full alphabet and raw-ID conventions; they do not supply typing-key semantics.

The pending-slot consumer must first derive oldValue from its actual getValue slot and PendingRealized, BEFORE selecting a bypass. A first read or an intervening false check may already have compressed the forest: bypass preserves expand-entry E, not necessarily original B or R. A bypass uses the derived old encoding, Frame B→E and pure_keeps to retain realization; no second representative action is executed. The driver still tests Empty after the wrapper, so a bypass returning Empty must not be reported as an accepted enumeration branch.

Only the fallback may invoke the current narrow_pending_complete packet at key=holeKey metadata.typing uv. That theorem derives its own complete oldValue from the same observed slot; any identification with the already classified oldValue follows from functionality of the SAME lookupNode heap oldHandle, not a new oracle premise or second execution. Its changed surviving branch retains actual Q, then actual F and exact write with scs. The original uv remains fixed for membership and key selection while the returned root is used ONLY as the write destination. Do not call the fallback producer merely to discover oldValue in a bypass: that would attach native narrowing effects that the source bypass never performs. The current83-payload narrowing declaration owner is frozen; its mathematical implementation is Root's separate current work.

## Precise open boundaries

Pruning.prunedPrograms is itself polymorphic in Typing/Key and accepts holeKey/fits/admits parameters. Parameterizing the wrapper by those SAME functions is a faithful operational model of that public caller, not a desired-narrowing-result oracle. Its equations prove no semantic pruning law. The concrete Specftacular call uses canonicalVariables(holeTypeOf typing rawInt), constantFits typeDepth skeletonSig, and flip typeAdmits. Native Types has PartialTyping substitution/instance variables and real unification/depth checks. No Lean definition of PartialTyping, holeTypeOf, canonicalVariables, extendTyping, constantFits or typeAdmits was found by exact-name search of all3684 current MicroCFTA files. Existing SourceTypingRules models a different bounded rule-row construction over abstract Ty; it cannot be substituted as the missing key/unifier model.

Thus native key realization, typing monotonicity, fits/admits soundness and same-key memo semantics remain open. The generic wrapper does not need assumed versions of those semantic laws to prove its literal branch equations and structural finite cache result. Full integration with the concrete phase4 caller needs the real typing representation/proofs later.

Nat model handles (Empty0, positive canonical identity+1), native NodeId/Int extraction and native raw UVar Int/Nat representation remain separate. The Mu test here uses a complete Value, not an unproved graph.node(handle) classification. EnumerationUntil still accepts a PURE OracleState→Nat→Nat→Nat narrow function and a graph; it has no explicit native heap/result carrier. The Value-level wrapper and explicit-heap pending suffix cannot be plugged into it by assuming an arbitrary callback equality. A later source-specific coupled-driver bridge must relate the actual observer/heap/handle and graph classification, plus real native cached-index maintenance. No full driver, typedTypes, pruning soundness, H6 strengthening, resource or convergence result follows from this proposed wrapper.

## Exact source cuts and identities

I read the listed source cuts and the relevant public inventories. The small NativeView/codec/Identity/Observation/Writes/Reread sources were already read completely in the unchanged current component and their live hashes were checked again. I do not claim a whole manual read of the large Haskell files or all typing foundations. Repository paths below are relative to /home/tritlo/Code/mcfta. Full-file bytes and hashes pin each defining source; no source snapshot or old evidence package is modified.

| Source | Exact cuts read | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `specftacular/src/Specftacular/Pruning.hs` | 85–141 | 16989 | `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` |
| `specftacular/src/Specftacular.hs` | 1099–1117 | 77825 | `b5a19e8c83908ff2de3cf3ee704731733224d96f36b7fb597afcd0fa017dbace` |
| `specftacular/src/Specftacular/Types.hs` | 804–814,975–1009 | 57422 | `e559f049d1f1c4397606e36580322ae5d3f256f1601a8d481ec25a1f4e429119` |
| `specftacular/src/Specftacular/Utils.hs` | 229–245 | 9246 | `2737df7df4bce7178e45c96db3bf550a0ce4c2d7d57ed131e2689071ec2e53ec` |
| `cfta/src/Data/CFTA/Interned/Type.hs` | 277–295,362–367,608–611,671–676,767–784 | 36883 | `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77` |
| `lean/MicroCFTA/SourcePruningRecordTypes.lean` | 23–55,70–103 | 13138 | `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf` |
| `lean/MicroCFTA/SourcePruningPositions.lean` | 17–99 | 11125 | `f43e8f437cd6a51d2aa3cf343ebebc046317fc0f40b1c4a67df8e293fac02b5d` |
| `lean/MicroCFTA/SourcePruningTemplates.lean` | 13–20 | 8380 | `1890878e308ec4debe67d6e74755bc00d93898f59a3a4ed1e5fa188c02899156` |
| `lean/MicroCFTA/SourcePruningNativeView.lean` | 21–79,147–177 | 10881 | `0cf2d0d30d1a231dd6a1c53dc8a78bc0b8c37972ff5fe3d55b2767e9f6f98571` |
| `lean/MicroCFTA/SourcePruningEnumerationNodes.lean` | 16–74 | 3546 | `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4` |
| `lean/MicroCFTA/SourcePruningEnumerationIdentity.lean` | 11–14,49–56 | 2939 | `e260eceaa5ed848c94155530c24ccca7c99092db0091b8b9e6174c33894e7361` |
| `lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | 19–25,45–54 | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` |
| `lean/MicroCFTA/SourceEqualityRequiredCache.lean` | 18–39 | 6081 | `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733` |
| `lean/MicroCFTA/EnumerationUntil.lean` | 94–124 | 8864 | `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137` |
| `lean/MicroCFTA/SourceTypingRules.lean` | 1–37 | 7561 | `883358821462c869be1ed01b284c674b62d5fa6519495661cd89e4bcb305fdc1` |

Current narrowing declaration provenance, preserved unchanged: /tmp/mcfta-pruning-enumeration-narrowing-20261024-proposal/.

- `/tmp/mcfta-pruning-enumeration-narrowing-20261024-proposal/public-header.lean.txt`: 3000 bytes, SHA-256 `2a8b797008c10807ca93716da381acfa570b766d623b57127b442475e7d561b5`.
- `/tmp/mcfta-pruning-enumeration-narrowing-20261024-proposal/pins.json`: 11575 bytes, SHA-256 `120678c343d16944236a44cd4d4423ed722731e4331f21e9e005dfa3ef0477a0`.
- `/tmp/mcfta-pruning-enumeration-narrowing-20261024-proposal/FROZEN.json`: 1098 bytes, SHA-256 `20415a7a7360c52e642c2e5c1d07ed010708e1189ce8790307ac2d9a8a26d23f`.

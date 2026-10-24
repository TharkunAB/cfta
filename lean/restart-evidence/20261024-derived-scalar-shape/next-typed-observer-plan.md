# Next typed pruning observer plan

Recorded: 2026-10-24 03:33:08 CEST. Read-only source assessment. No compiler, proof draft, repository edit, or native execution. Arity authored the existing pure template helpers and some earlier observer foundations; this is a new source/API composition assessment, not an independent reproof of those foundations. Root owns integration and sealing.

The next callback is feasible as a sequence of existing compression-preserving observers. A complete native `narrow`/`emptyAt` model needs an additional precise node view: the current enumeration graph does not distinguish Mu from the broader recursive boundary. Keep that requirement explicit.

## Exact source behavior

1. `recordTypes` (Pruning 107–112) updates type positions from the incoming type set and raw fragment. With an empty catalog it skips `templateOracle` completely. Otherwise it runs the existing concrete oracle and returns its updated pending groups. The open-hole set and typing stay unchanged.
2. `typedTypes` (113–126) tests the incoming type set, not `types'`. Only a fragment event with `prune = false` at a raw current ID absent from that incoming set enters the typing branch. It performs a fresh partial render even if `recordTypes` already rendered through its template oracle. The actual intermediate enumeration states must remain separate.
3. `extend rawCurrent (openProgram false partial) typing` is the actual pure source parameter. `none` rejects and returns the metadata from `recordTypes`; it performs no open-hole reads. On `some typing'`, delete raw current from open, then insert all `programHoles false fragment`. A current ID that occurs in those program holes is reinserted.
4. `IntSet.toList open'` reads the unique raw IDs in ascending numeric order. Run every `getUnexpandedNode` read with `mapM`, in that order, before computing pure `or`; do not stop on the first dead hole. `none` contributes false without calling `emptyAt`. A true result rejects with the earlier metadata, while all representative compression from those reads remains in the final enumeration state.
5. `narrow` (127–131) returns its node unchanged for Mu, then for a raw current ID in the type set. Otherwise it calls `narrowAt`. `emptyAt` (132–134) returns false for Mu only. A union is not exempt. Keep the renderer's separate, broader boundary: `recursiveBoundary` recognizes both native Mu and union (Type 608–611), and partial rendering uses that broader test (Enumeration 1045).
6. `narrowAt` (136–141) filters actual `nodeEdges`, then applies the actual smart `Node` constructor. For exact ordinary Top app/4 and filter/2 it tests `admits` on the first child. For any one-child edge it tests both `admits` and `fits` on the full symbol. All other edges remain. `memo2` is a per-`prunedPrograms` cache of this pure function; it does not modify the enumeration state.
7. `programHoles` (147–157) retains raw IDs only at program positions: app function then argument, and filter term. It ignores concrete type subtrees and all other concrete program shapes. `typePositions` (164–175) follows literal right-fold order; it records type holes in annotations/markers and all children under type positions. Preserve full labels and exact ordinary literal recognition.
8. `openProgram` (199–213) retains concrete full labels. A type hole becomes ordinary `?`; a program hole becomes ordinary `?program#` plus the decimal raw ID; truncation becomes ordinary `Mu`. Program app/4 and filter/2 recurse with their exact type/program positions; all children of other concrete shapes are type positions. This is total on partial terms. Do not replace it with `openTypes`, which raises an error on a program hole (182–194).

Raw IDs in pending groups, type membership, open membership, and generated placeholder names must remain raw. Representative lookup occurs only in the existing observer actions. Nat IDs and ascending finite lists can model nonnegative native UVar/IntSet values; the native Int range, Text decimal formatting, and symbol interning correspondence remain explicit representation obligations.

## Minimum additive decomposition

A. Add the pure source helpers `programHoles`, `typePositions`, and `openProgram`, with the existing `Fragments.Fragment`, `Language.Term`, `EnumerationState.PartialSymbol`, and `SourcePruningTemplates.Symbol` (full `Label FullSyntax.Formula`). Reuse a canonical ascending unique Nat list for IntSet observation; `EnumerationBuilderCaches.canonicalIds`, its membership, sortedness, and no-duplicate lemmas already supply this algebra. Define insertion/deletion with their literal set effect and prove the ascending traversal equation. No new term or pattern datatype is needed. `typesLast` and `atTypes` are small pure additions; they do not require new state reads.

B. Resolve the immutable native node view before claiming complete source fidelity for `narrow`/`emptyAt`. `EnumerationState.Graph.node` has only empty/alternatives/recursive/unresolved, and its recursive tag is the broad rendering boundary. It cannot supply the Mu-only discriminator. Existing `InternedConstructorTemplates.Value` already retains separate node/union/mu tags and full child records; reuse it if a stored-node view is required. Do not add an arbitrary `emptyAt` callback as a substitute for the source function.

The view must also implement the actual union/unfolding `nodeEdges` closure (Operations 161–182), including its unresolved-union-reference error, and smart `Node` construction. `matchMu` succeeds exactly on `InternedMu` (Type 767–784). `mkNode` discards edges with EmptyNode children, sorts/deduplicates survivors, and returns EmptyNode for no survivors (543–586). Thus `emptyAt` is not justified by checking only whether the pre-constructor filtered edge list is empty. Existing `EnumerationBuilderCaches.construct`/`rows_empty_iff` cover the ordinary cache representation under their actual canonical-cache premises; they do not by themselves prove the recursive/union view correspondence. Native-view realization is a separate concrete obligation, not a hypothesis that already asserts the desired callback result.

C. Define literal `recordTypes` and `typedTypes` on the existing enumeration action, with a tuple of pending groups, type IDs, open IDs, and typing. Keep pure source parameters `extend`, `holeKey`, `fits`, and `admits` shared and fixed. An internal ordered open-hole observation helper should use `getUnexpandedNode` and the concrete pure `emptyAt`; it returns the complete list of Booleans before `or`. Prove its frame, paired agreement, more-fuel retention, and finite one-sided transport by list induction. Then compose existing oracle, fresh renderer, pure extension, and that helper at the actual middle states.

This decomposition needs no new scheduler or driver run. It does not establish typing/pruning soundness. The source's semantic caller requirements on `extend`/`fits`/`admits` remain separate from observer congruence.

## Public proof premises and conclusions

Use the existing success relations and literal callback result `(prune, metadata)`. Fix the same immutable graph/node interpretation, full-symbol catalog, raw current ID, event, initial metadata, and source pure functions on both sides. For paired agreement require `Frame left right`, `UnionFind.Total left.representatives`, and two actual successful callback observations at independent `leftFuel` and `rightFuel`. Conclude exact result equality, including pending order/duplicates and open/type/typing metadata, plus `Frame leftAfter rightAfter`.

For one-sided transport require only that frame, left totality, and one actual left successful callback. Construct some finite right fuel and a successful right result with exactly the same metadata, plus the complete final frame. Do not assume a right success, equal fuel, Safe/Finished, accepted completion, a readable-all-slots oracle, or the desired output certificate. The actual left read supplies each slot needed for existing getUnexpandedNode transport. Prove single-run frame preservation and `Retains` under increased fuel separately.

The frame is the complete installed relation: equal counter, values, obligations, recursion ancestry, and expansion ancestry, plus equivalence of every `Reaches uv root size` fact. Preserve exact root IDs and sizes. Literal equality of whole forests is neither required nor promised. At every composed success, propagate totality through the actual intermediate frame. Existing read-only-oracle properties that require final state equality cannot replace these theorems.

Reuse `EnumerationObservations.getUnexpandedNode_success/agrees/transport/moreFuel` (NodeObservation 24–76), `expandPartial_frame/moreFuel`, `expandPartial_agrees`, `expandPartial_transport`, and `SourcePruningOracle.oracle_frame/agrees/moreFuel/transport` (242–318). Node observation is precisely the projection of `getValue`, whose native implementation first finds/compresses the representative (Enumeration 415–428, 1411–1417). For a finite ordered list, obtain each right bound at its actual middle state, combine bounds by addition, and raise earlier/later observations with existing `Retains` lemmas; preserve each constructed intermediate and final state. This is the same finite-bound composition already used by the concrete template oracle. Frame-only list composition can reuse `EnumerationSchedule.mapM_invariant` (1061–1078).

Recommended first component: pure position/open-program helpers and literal recordTypes frame/agreement/transport. The full typedTypes proof then adds only the ordered read helper and actual native node view. Do not claim the complete source callback until the Mu/union/smart-constructor view is fixed. No Haskell defect is asserted by this assessment; this is a model coverage gap.

## Inspected source identities and exact cuts

Each identity below is the full live file. A cut hash covers its exact UTF-8 line bytes, including line endings. No executable was imported or run.

- `/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Pruning.hs`: 16989 bytes, 350 lines, SHA256 `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61`.
  Cut 85–141: 2966 bytes, SHA256 `cf08ffba3ed9386416a8d65c480945f8297d88b6a81d7579766c4c8777e24c7f`.
  Cut 147–175: 1453 bytes, SHA256 `ae2f5ab0c81b828aff446fbbb2d0fe48cad6467dbeb839d15d286a93ef79c17a`.
  Cut 182–213: 1789 bytes, SHA256 `c6d1d18da667ee1c9ebdd4e3705b31f60a839d18977ed34a80fcbc233e0a963f`.
- `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs`: 71269 bytes, 1587 lines, SHA256 `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.
  Cut 415–428: 515 bytes, SHA256 `f90c73a0aac78b8cc634cec70186d716a8e401a95b01fb46c7d89716666bb1fc`.
  Cut 1038–1046: 564 bytes, SHA256 `f8337b9caee82abe59652dc6c3b011ecf4859afc9fb2dee1edc3bb4b3efd1d36`.
  Cut 1411–1417: 288 bytes, SHA256 `e9b101f416161ed133d146f4052a9204ac57040d633a84b3cf80addb40f01c9b`.
- `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Type.hs`: 36883 bytes, 922 lines, SHA256 `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77`.
  Cut 543–611: 2640 bytes, SHA256 `c1bf2d7c0ffc68555d6902fef38a2c653a1c74fff89d227e3847b3d7eff98e7f`.
  Cut 671–675: 148 bytes, SHA256 `045b06616a1bedeadcc06f288327d42c360a81c5b26d1b27a4139df70d5d4eda`.
  Cut 767–784: 834 bytes, SHA256 `752aedd5a52f6c2aa95ef747da33b1097981403c43b046b2ae9d308577784c75`.
- `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Operations.hs`: 38260 bytes, 887 lines, SHA256 `1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836`.
  Cut 154–182: 1337 bytes, SHA256 `ff97ff2caf694d6b4b15aa4dc31b816497ceaa2dc109c45efa903f0093155986`.
- `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Symbol.hs`: 5657 bytes, 148 lines, SHA256 `31983078475d136d2e69f5d94461f56f7c2fa3b3822144be1eee324ba0637f02`.
  Cut 54–84: 1290 bytes, SHA256 `dbf3d18ed9bdf45ed855c6448b6d7b04662581b80abf65e2bd585e30dbd20b49`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationState.lean`: 33489 bytes, 699 lines, SHA256 `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.
  Cut 36–53: 653 bytes, SHA256 `f94dabb44627efc863f9fd14ee18a462abe7d92092dea58a1ab1cd9fdb182f82`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCompressionFrame.lean`: 8220 bytes, 145 lines, SHA256 `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375`.
  Cut 19–52: 1938 bytes, SHA256 `11e80dfe09f994aa810fc5ee891870daf5cb18ec8c432bee65df4ef45d0bdcac`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationObservations.lean`: 6136 bytes, 105 lines, SHA256 `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab`.
  Cut 31–103: 5030 bytes, SHA256 `22cb0513c5e5b37cf62931e3a3dc7f938d04739f26e8b070726c94745fa23f80`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationNodeObservation.lean`: 4323 bytes, 78 lines, SHA256 `0dc7f259885a4c5a914aed2d7a62030b18cc87fc37962ffe438c146b6459d06d`.
  Cut 18–76: 3730 bytes, SHA256 `5d8e3f4354109ad8c6fae8ed0b1a3fc901031dd513f03db33b2490cfaacad2c8`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationPartialObservation.lean`: 4692 bytes, 87 lines, SHA256 `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc`.
  Cut 20–87: 4004 bytes, SHA256 `2a63d1423aea9169885544f046c1fd4c987b7ef0eab53b74b4cd84da12971fe9`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationPartialCongruence.lean`: 9302 bytes, 141 lines, SHA256 `7452999a98756fdb92be845b4eb52f08926c5a12ce9c42752df1333d457bcb60`.
  Cut 36–141: 8033 bytes, SHA256 `82a8375c4f55130e207941b5c3bc87d3fa4b65db2fa2a9d98a7f0e68dc6c938b`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationPartialTransport.lean`: 9581 bytes, 155 lines, SHA256 `cfb86bcdf59c125625bb78f0fea7da467789adc162f27c4f1a4e45f630b5674c`.
  Cut 37–155: 8204 bytes, SHA256 `01d032bf02fd20fc0e81e5978d59742f49d2839339d541e6424ab46dcc5f9269`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationExecution.lean`: 30176 bytes, 478 lines, SHA256 `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346`.
  Cut 35–63: 1549 bytes, SHA256 `b1ee35731793270c8c3bdc1617dda608d2a4c173d08036cb917e38ddbf2263ca`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationSchedule.lean`: 86287 bytes, 1348 lines, SHA256 `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45`.
  Cut 1061–1078: 1270 bytes, SHA256 `253ec9dcb4b848128e77a15c22ca550305e5884dd03b8b213bc3ab1b78bfe5ac`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningOracle.lean`: 20956 bytes, 320 lines, SHA256 `cb782c5dcc18b8dfe87927778523df97f38c9cf3fe1e9946e4f24f1ffbdc69e0`.
  Cut 1–67: 3088 bytes, SHA256 `71433be667517d834494d2d6ff8616b59db5a4e0cdd9899950b5281b1b43567a`.
  Cut 99–153: 4018 bytes, SHA256 `70c721274b3327bd14b4ad2e0ff0251b3d79406fce091217f4ea1ef6a91d97f9`.
  Cut 193–221: 2047 bytes, SHA256 `13e01bf551a0e0fc039d62e55f2d936ed83e41416fe824484253df3669b67d62`.
  Cut 242–318: 5344 bytes, SHA256 `67a3ae75cf955d8a762ff4db2992c6f4d4a5def7b46f140551826a48691df10f`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningTemplates.lean`: 8380 bytes, 171 lines, SHA256 `1890878e308ec4debe67d6e74755bc00d93898f59a3a4ed1e5fa188c02899156`.
  Cut 1–24: 987 bytes, SHA256 `55e7a2de36ae77d3cc2e950fe2eee4eb4bf147c2f5a7f0cd1440ee876465d7c4`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedConstructorTemplates.lean`: 46073 bytes, 805 lines, SHA256 `75aeb072ce0cfb7bc8bad40843184743281de8aeac1001c13ad941692d23e3f8`.
  Cut 20–40: 1060 bytes, SHA256 `269579622d8579e04acdd68792fc244257ccaa2fe0d5ad35e59081fc2558fc7a`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationBuilderCaches.lean`: 27843 bytes, 451 lines, SHA256 `f4882be07a73362a667a994f9e37344b9fb4619565dcf53ca0e857ecd21ccb9d`.
  Cut 13–39: 1566 bytes, SHA256 `0bde4a13bb5765014f891189e8e55849433e4c1bf4c15e19684209f57e6975d6`.
  Cut 104–123: 1161 bytes, SHA256 `dc4897cdae36143525fa9993b88681e4b38cfa5e5b4dc86548d2c8b689b7765b`.
  Cut 439–449: 521 bytes, SHA256 `11e683d1a573d02eff36080f159a27fb71abb1ebe75e62013a9417ff7bd536ad`.

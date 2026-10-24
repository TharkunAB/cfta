# recordTypes, typesLast and atTypes source contract

Reviewed at 2026-10-24 03:58:54 CEST. Status: **SOURCE_CONTRACT_CLEAR** for the concrete wrapper described below. I read the native callback and selector definitions, complete typePositions definition, relevant native state/monad/caller signatures and the installed concrete template-oracle definitions and public frame/agreement/retention/transport contracts. I did not write a candidate, run a compiler or native program, change source files or mutate Git. No native defect is established by this review.

## Exact inputs and branch results

Native `prunedPrograms` initializes caller metadata to `([], IntSet.empty, IntSet.singleton 0, start)`. This metadata is separate from the nondeterministic `EnumerationState`. The callback receives `(pending, types, open, typing)`, the incoming **raw** UVar and either `Left fragment` or `Right node`. `pending` is a list of pending groups, each itself a list of pattern/raw-ID pairs. The wrapper returns `(prune, (pending', types', open, typing))` inside the actual enumeration monad. It does not run a new scheduler or allocate a second enumeration state.

Root's proposed `Metadata Typing` with these four fields is a direct representation. `Typing` can remain opaque and need not have an equality decision procedure. The full source symbol is the existing `SourcePruningTemplates.Symbol`, including refinement. Nat lists for `types` and `open` represent the observable ascending, duplicate-free IntSet enumeration. Their canonicality concerns **set representation**, not union-find representatives. Keep pending order/duplicates and candidate order separately; do not sort those lists.

| Input/catalog | Type field | Callback result and other metadata |
| --- | --- | --- |
| `Left fragment`, empty catalog | Apply typePositions with the Boolean raw incoming `uv ∈ types`, using the incoming types field. | Do not invoke the concrete oracle. Return false, unchanged pending, updated types, unchanged open and typing. The action is pure on enumeration state. |
| `Right node`, empty catalog | Exactly the incoming types. | Return false and the exact incoming metadata, without an oracle call or state read. |
| `Left fragment`, nonempty catalog | The same deterministic typePositions update from incoming raw membership. | Run `SourcePruningOracle.oracle` on the original pending/current/input. Keep its actual prune flag and pending result, with the computed types and original open/typing. This applies even when the prune flag is true. |
| `Right node`, nonempty catalog | Exactly the incoming types. | The source invokes its concrete oracle, whose checked `oracle_inr` equation is pure false/original pending. Thus the wrapper returns the exact incoming metadata and unchanged enumeration state. |

Two shortcuts would change the source. Returning the whole original metadata for an empty catalog would omit the Left typePositions update. Conversely, always invoking `oracle []` would not implement the empty-catalog branch: that oracle can still resume existing pending groups or render/read a raw fragment hole. The source explicitly skips it. There is no representative read when testing whether the incoming uv is a type. Do not test membership of a normalized ID, of a hole occurring inside the fragment, or against the already-updated types field. Do not feed metadata/type results into an arbitrary replacement oracle.

`typePositions` is pure. At a type-position hole it inserts that raw ID; a non-type-position hole leaves the set alone. At a node already in a type position it recursively treats every child as a type. Otherwise, exact full-label app/4 handles annotation and marker as type children, function and argument as program children; exact filter/2 handles annotation as type and term as program. Every other node treats all its children as types, including malformed app/filter arities. The native nested foldr order is literal: app program argument then function, then marker then annotation; filter program term before annotation. Its observable IntSet result is canonical regardless of traversal order. The helper must preserve source branch distinctions without inferring a typing invariant.

Required confirmed the planned helper interface `SourcePruningPositions.typePositions (isType : Bool) (fragment : Fragment SourcePruningTemplates.Symbol) (types : List Nat) : List Nat`. Its intended implementation normalizes only at insertion and keeps the native foldr structure. That interface is coordinated planning, not a claim that I have reviewed or compiled the forthcoming helper candidate. For native set fidelity, source-observed input lists must be sorted and duplicate-free and insertion must preserve that representation. Noninsert branches should retain their actual input list, as source sets are already canonical; do not silently broaden representation claims to arbitrary malformed list encodings.

## The two pure selector contracts

`typesLast` first calls the existing concrete `SourcePruningTemplates.order pending candidates`. If it finds a raw ID waited on by any pending pair, return that same first candidate **even if it is in types**. Only when that result is none, return the first supplied candidate whose raw ID is absent from types. The function ignores open and typing. It preserves the supplied candidate traversal order, and an empty candidate list gives none. Canonical ascending type sets do not justify reordering candidates. This is a direct local selector contract, not yet an identification of the native cached scheduler's candidate list.

`atTypes` is true exactly when the raw ID belongs to types **and every pair in every pending group has a different raw ID**. This is the native nested `all`; empty groups and an empty pending list satisfy its waiting exclusion vacuously. Pattern contents and the open/typing fields are ignored. A pending occurrence with the same raw ID makes the result false. An alias in the same union-find class does not count as that same raw ID unless the IDs are literally equal. Preserve that comparison instead of repairing it by representative normalization; any needed source invariant for pruning remains a separate question.

## Reuse of the actual observation proofs

Use the existing `EnumerationState.Oracle Symbol Guard (Metadata Typing)` shape and existing full `State`, `EnumerateM` and `Success`. The graph, catalog, raw current ID, fragment/node input and incoming metadata must be the same between paired observations. The concrete oracle already proves: frame from totality plus one actual success; agreement at independent successful fuels from a full input frame and left totality; exact successful final-state retention under fuel addition; and construction of a finite right success from one left success and a frame. It is not an arbitrary-oracle theorem.

The wrapper's empty-catalog paths use the actual pure-result laws. Nonempty paths use one actual oracle action followed by pure metadata reconstruction. Existing `oracle_frame`, `oracle_agrees`, `oracle_moreFuel` and `oracle_transport` then supply the wrapper results directly through bind success. In agreement/transport, deterministic type classification is equal because incoming metadata and input are equal, and original open/typing are copied. Full final-state frames must be retained. Transport must construct its independent finite right fuel; equal initial fuel across compressed forests is not justified. No desired result, right-success certificate, Safe/Finished, canonical-current or pruning-soundness premise is needed for this observation component.

## Fidelity boundaries

The native UVar conversion is a raw Int wrapper/unwrapper, not a representative lookup. Nat IDs require a nonnegative faithful encoding of observed native IDs; machine overflow/range bounds remain separate. Set extraction, native IntSet layout and native Text/interning extraction are not proved by choosing canonical Nat lists. Exact full labels and ordinary `.top` app/filter tests remain necessary. The Lean state retains counter, forest, values, obligations and both ancestry fields; native state also has maintained caches, edge-order function and recursion flag. Existing full modeled Frame does not by itself prove extraction of those extra native fields or cache maintenance.

This wrapper does not execute the later `typedTypes` extension, inspect open holes, invoke `extend`/`holeKey`/`fits`/`admits`, prove narrowing keeps desired edges, implement stopping, or show that a partial term has a completion. Initial membership/typing invariants, representative protection, native mutation histories, whole-driver realization and semantic pruning remain separate. Keep earlier H6 and H23 claim boundaries unchanged.

## Exact source cuts

| Cut, with original LF bytes | Bytes | SHA-256 |
| --- | ---: | --- |
| `specftacular/src/Specftacular/Pruning.hs:85–112` | 1336 | `1ca7c150eefef05017df77341a554aff8203d6d4420f5a508398fd925c8f8543` |
| `specftacular/src/Specftacular/Pruning.hs:164–175` | 731 | `c2500918ea758bae810d111581db0be084439441fb274609d4fbd2ef5683d5ac` |
| `specftacular/src/Specftacular/Pruning.hs:220–251` | 1730 | `14f8d0ef556051dbdb61cb2b74c49eeddbbbe5dc1bea7329b3af198f6817fa39` |
| `cfta/src/Data/CFTA/Enumeration.hs:228–269` | 1997 | `d1f7a7c556587345baebc15f5dac7fa56e8cc6182d40598de614f1201d7e8928` |
| `cfta/src/Data/CFTA/Enumeration.hs:328–351` | 846 | `c69c6e0d09958d0ba0398b27f6543a4a6ff5d6c9f88fbb54fe1eb3f9e1cb33e2` |
| `cfta/src/Data/CFTA/Enumeration.hs:1180–1194` | 625 | `ac7188f13e1c4c7790b458881bd36e9a7901be7f15aa6cd6735e78235bcf432c` |
| `cfta/src/Data/CFTA/Internal/UnionFind.hs:39–65` | 642 | `b7cf65fc291e82673872a8be596b7914b63aa08f5670363876dbcc8054840420` |
| `lean/MicroCFTA/EnumerationState.lean:67–86` | 859 | `cdcbbd59bcc3172024a093b9fb08491afd1560ac46893c77d72ae0372052ae0c` |
| `lean/MicroCFTA/EnumerationState.lean:296–298` | 236 | `7ca2f73beca1b1f74b043eea3f0f873c31ff1f6856eed8fdf255c45bae6e9d0c` |
| `lean/MicroCFTA/SourcePruningTemplates.lean:120–123` | 251 | `8ca9db4674546bff03c711ffa54cb0cf509d94bdd031175069234a036df095d1` |
| `lean/MicroCFTA/SourcePruningOracle.lean:56–68` | 781 | `154cf3e40a786c81e682aca07cf054b4f83f5afe68042a7fb1f6083e5b532902` |
| `lean/MicroCFTA/SourcePruningOracle.lean:242–320` | 5379 | `0606b8c1a9554f58afe31f6681a0f7383a8b394bf6c83ee267fe421e7aeae559` |

Complete file identities for the cuts above:

- `specftacular/src/Specftacular/Pruning.hs`: 16989 bytes; `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61`.
- `cfta/src/Data/CFTA/Enumeration.hs`: 71269 bytes; `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.
- `cfta/src/Data/CFTA/Internal/UnionFind.hs`: 4723 bytes; `096db1d6a4d693cebfc9cb643486434baee93e3379c5a411d3edd556d102d434`.
- `lean/MicroCFTA/EnumerationState.lean`: 33489 bytes; `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.
- `lean/MicroCFTA/SourcePruningTemplates.lean`: 8380 bytes; `1890878e308ec4debe67d6e74755bc00d93898f59a3a4ed1e5fa188c02899156`.
- `lean/MicroCFTA/SourcePruningOracle.lean`: 20956 bytes; `cb782c5dcc18b8dfe87927778523df97f38c9cf3fe1e9946e4f24f1ffbdc69e0`.

# Smallest current checked class-edit port

Read-only proof inventory. No proof changes or builds. The upcoming checked SharedTarget State/Force/Leaf APIs are used as planned interfaces here; this note does not certify the in-progress Leaf proof.

## Recommended first endpoint

Add one checked edit graph, with the old `EditNode` / `EditChildren` / `EditRows` / `EditList` constructors specialized to `SourceCurrentAllocatedSharedTargetState.State width`. Use the NEW checked Leaf at `.editAt`. Ordinary reconstruction and recursive Head reads advance the SAME checked state through `advancePhysical`, leaving target slots and the merge table unchanged. Then prove one compiled `Class` endpoint before a multi-class pass.

The effect result must be `∃ nextInventory, SharedTargetState.Ready formulas solver nextInventory record captured base after ∧ Effects ... ∧ ...`. The current inventory can change at every leaf query. It must not be equated with the historical slot inventory. A fixed current-inventory result type would reintroduce the gap already removed by the new State/Force/Leaf layer.

## Literal source schedule

`Equality/Operations.hs:211` applies `foldr reduceEClass` after required preparation. Each class therefore captures the forest returned by its actual tail. Lines 236–244 build all callbacks from that same captured `ns`, in `Set.toAscList` class-path order. Each callback forces a shared target from the OTHER paths, then intersects that target with its current leaf input. The first-seeded `intersectList` is at lines 228–230.

`editAll` at lines 317–342 builds its trie with a right fold. A leaf replaces descendants; an existing ancestor leaf blocks a deeper insertion. The list-root leaf is ignored. Ordinary rows use `setChildren`; Mu/union nodes use `Node (nodeEdges n)` before the same edit; a reached Rec errors. Do not add an identity rule for an arbitrary empty `EditBelow` at a node.

IMPORTANT: `Interned/Type.hs:391–400` documents and implements the same-arity `setChildren` fast path. If the rebuilt child list has the original length, it directly calls `internEdge` with the original symbol and full raw constraint. It DOES NOT call mkEdge or the full equality accessor. The positional edit traversal preserves child-list length. This justifies raw `makeEdge` in the checked edit graph while retaining the operation cache. Prove that length equation explicitly. Do not introduce new equality allocations or assume a universal conjoin/constructor closure premise. A different-arity replacement would need the actual mkEdge fallback, but this traversal does not change arity.

The graph retains the existing completed serial child/row schedule. IntMap fold/list spine behavior alone does not prove GHC forcing order, eager child values, or exact allocation order. No runtime schedule equivalence should be claimed.

## Directly reusable pure compiler/domain facts

- `SourceEqualityEdits.build_valid`: literal signed-map compiler validity.
- `SourceEqualityEditCompiledPaths.build_leaves` (line 67): disjoint original edits give an exact permutation of retained callback occurrences.
- `...build_matches` (line 81), `build_not_leaf` (line 91), `list_condition_exact` (line 100): exact callback path conditions and the nonroot list-root exclusion. These are pure and do not mention the old native engine.
- `SourceEqualityClassEdits.coherent_supported`, `edits_disjoint`, `supported_nonroot`, `edits_nonroot`, `conditions_exact`: derive compiler premises from actual Record.Coherent and active class paths, with exact Nat-to-Int conversion.
- `SourceEqualitySharedClassEdits.compiled_allowed`: every callback token is an original class path.
- `SourceCurrentEditDomains`: `Populated`, `HasLeaf`, `Safe`, `ChildrenSafe`, `RowsSafe`, `Transport`; `build_populated`, `build_hasLeaf`, `ordinary_rows`, `children_tail`, `recursive_closed`, `closed_safe`, `transport_forest`.

At a leaf, `Safe (.editAt path) input` entails `input.free=[]` from the retained empty residual path. At an entered recursive head, `HasLeaf + Safe + Recursive` entails whole-head closedness via `recursive_closed`. Only these actually selected nodes need closedness. Unselected ordinary children remain open.

The historical class modules' `compiled_safe` is private. Reprove the short bridge from `build_leaves` to `ChildrenSafe` in the new wrapper, or expose it in a NEW helper. Do not edit old files to make it public.

## Exact reusable constructor and head effects

Use current `Ready` fields at the reached checked heap, not old `IdleReady` as an execution transfer.

- `SourceEqualityRequiredCache.edge symbol guard children heap ready available` (line 53) gives Keeps, EdgeResident, and exact returned ordered children. It has no closedness premise.
- `SourceEqualityRequiredSemanticCache.edge` (line 32) retains SemanticReady for those same available children.
- `SourceEqualityAnnotationHeap.makeEdge` + `run` (lines 84/67) preserve physical fields when the original guard has FieldAvailable in the CURRENT operation cache. Obtain that check from the original resident row, then use `FieldAvailable.grows` through the child effects. Edge interning leaves nodeRecords unchanged, so stored CostHeap is unchanged.
- `SourceCurrentRequiredHeapEffects.node_constructor property edges heap semantic costs fields resident` (line 24) gives Keeps, SemanticReady, CostHeap, physical Heap property, and Available for actual `makeNode`, WITHOUT whole-row closedness. Instantiate property with `FieldAvailable currentOperations`.
- `SourceEqualityOpenOrdinaryHead.node` (line 23) is the open-resident node constructor law. `EqualityLeafProjectionPhysical.makeNode_edges` reads back exactly `canonicalEdges (surviving edges)`. This handles filtering/canonical hits; do not claim output rows are the unfiltered list.
- `SourceEqualityRequiredHead.complete value heap ready available closed` (line 23) constructs finite actual Head plus Keeps, Available, closedness and Ordinary. The local closedness is derived from Safe above.
- `SourceCurrentRequiredHeapEffects.head property actual semantic costs fields available` (line 38) gives actual open head-read Keeps, SemanticReady, CostHeap, physical Heap property and Available. It has no closedness or future output premise.
- `SourceCurrentRequiredQueryMemos.head_memos actual semantic costs available memos valid` (line 81) gives actual HeadReads and final same-heap Valid, unfolding Extends and unchanged query pair. It is trace-independent of the old shared edit state and can be reused directly.
- `SourceEqualityRequiredHeadLanguage.head_exact` gives exact independent language for the selected closed recursive head. `MergedColdInterpretation.makeNode_exact` gives ordinary reconstruction language from actual resident rebuilt rows, without whole-forest closedness.

Lift these heap effects with `SharedTargetState.Ready.physical` (line 125). It derives current checked Ready and At from actual Effects, retains the class slots and merge memo, and keeps operations unchanged for constructor/head-only work. `Ready.advance` handles actual checked query effects when the inventory changes. Do not replace either with a future Ready oracle.

## Minimal inductive proof order

1. Port the raw graph and actual-prefix ranges from `SourceCurrentMemoSharedEditGraph` / `...Ranges`, replacing only the old shared state, advanceHeap wrapper and leaf graph. New leaf ranges are ForceRanges plus WordRanges after the ACTUAL Force return.
2. Prove physical effects/domain transport by actual graph induction. Return existential current inventory, current SharedReady, Keeps/Extension, result residency, slots Retains, merge Extends, and All₂ Transport for children/rows. The leaf result is closed from the new Leaf receipt. Raw constructors discharge field/cost obligations as above.
3. Prove finite edit completion from the range plan. At recursive nodes derive closedness, construct Head, and reuse its actual result. At selected children and later rows use the actual completed prefix to select the next range plan. No completed body/native callback premise is necessary.
4. Port language bounds using concrete PCS holds and new `Leaf.Receipt.narrows` / `.preserves`. The old `SourceCurrentMemoSharedEditLanguage` is a structural template, not a theorem transferable to new execution. Its compiler-condition proof can be repeated over the new graph. No generic conjoined law or old uncached Produced invariant is needed at the new concrete leaf.
5. Add one compiled class endpoint using actual Record.Coherent/active, domains, the signed edit compiler facts, and class-local `SharedTargetState.initial`. Only this initialization clears slots. It retains the actual checked state and merge memo from entry.
6. Add the class right fold, capturing each tail-returned forest/heap/current inventory/merge table, with fresh slots only for that class. Use Transport to derive the next head's selected domains. Finish with literal empty propagation; `SourceCurrentClassFoldDomains.propagate_available`, `propagate_transport`, and `propagate_domains` are pure heap/value facts reusable unchanged.

## Real remaining assumptions

Initial checked Ready/At, actual captured forest availability and selected path domains, coherent active physical records, legitimate uniform warm merge CacheCovers, initial global Valid/fourth Correct, and actual-prefix machine range plans remain inputs. Record/path/order derivation and caller initialization can later come from the existing physical precheck/Scan/Required endpoint. Do not assume whole forest closedness or reset native/domain/equality/merge tables to discharge them.

The full checked trie-edit/class-pass graph, its completion/domain/language induction, and its primitive/global-event receipts are not yet implemented. Existing old shared-edit worker soundness/stability theorems describe the old native engine and cannot be applied to the new checked one. Exact GHC delayed demand, publication/concurrency, native containers/IDs, and general constrained outer-caller termination remain separate after this bounded port.

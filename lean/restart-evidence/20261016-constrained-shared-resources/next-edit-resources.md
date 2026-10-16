# Exact edit count and profile induction

Reviewed 2026-10-16 21:05 CEST. This is a read-only next-proof plan. No production file, build, Git state, or older evidence changed.

## A source position receives at most one callback

The finite ordinary traversal cannot invoke two edit callbacks at one literal input position. This claim concerns positions, not identities. Two equal children in different rows are two positions.

The reason is the literal graph in `lean/MicroCFTA/SourceCurrentAllocatedSharedEditGraph.lean`:

- `EditNode.leaf` at line 36 invokes one Leaf and does not recurse into its result.
- `EditNode.empty` at line 38 invokes no Leaf. An `.editAt` on Empty instead uses the leaf constructor and invokes one Leaf.
- `EditNode.ordinary` at line 39 traverses its original row list once, then rebuilds the node. It does not edit the rebuilt result.
- `EditChildren.selected` at line 56 edits the original head once, then advances the index and visits the original tail. The returned head is only prepended to the returned list.
- `EditRows.cons` at line 67 edits the original first row's children, rebuilds that row, and then visits the original row tail. It does not traverse the rebuilt row.
- `EditList.leaf` at line 78 ignores a callback at the forest root. It invokes no Leaf. `EditList.children` delegates to the child scan.

This count argument does not need compiler Valid, Allowed, Populated, or Safe. Even duplicate entries in a malformed signed child map do not cause a second visit: the graph performs one `SourceEqualityNeededMap.lookup` for each child index. Lookup selects one entry, not all matching entries (`SourceEqualityNeededMap.lean:13`). The compiler additionally derives ascending unique entries (`SourceEqualityEdits.build_valid`, line 77). An edit trie has either a callback or child edits at a node, never both. `insert` at line 27 preserves that distinction; duplicate and ancestor edits resolve in the source right-fold order.

The recursive constructor at graph line 43 is the limit of this argument. It exposes a new head and continues below it. The current ValuePositions count treats recursive and union heads as opaque. Finite ordinary input domain excludes this constructor. Do not extend the position bound to general Mu/union execution without a separate exposure argument.

## Minimal pure count certificates

The raw graphs are propositions. Do not define a Nat-valued callback counter by eliminating their proofs. Use mutually indexed Prop relations `NodeCount actual calls`, `ChildrenCount actual calls`, and `RowsCount actual calls`, plus `ListCount actual calls`. Each relation retains the exact raw graph and its physical indices. Their constructors record these equations:

| Raw constructor | Leaf query count |
| --- | --- |
| node leaf | `1` |
| node Empty below | `0` |
| node ordinary | row count |
| node recursive | exposed body count; excluded from the finite ordinary bound |
| children nil | `0` |
| children unselected | tail count |
| children selected | selected head count plus tail count |
| rows nil | `0` |
| rows cons | child count plus later-row count |
| list leaf | `0` |
| list children | child count |

The four minimal theorems are:

```text
node_count     actual DNode(input)     -> exists calls, NodeCount actual calls     and calls <= Positions.node input
children_count actual DChildren(input) -> exists calls, ChildrenCount actual calls and calls <= Positions.children input
rows_count     actual DRows(input)     -> exists calls, RowsCount actual calls     and calls <= Positions.rows input
list_count     actual DChildren(input) -> exists calls, ListCount actual calls     and calls <= Positions.children input
```

Prove the first three together with the actual graph's mutual recursor. Generalize the input-domain premise in each motive. The recursive case contradicts that premise. The leaf case uses `Positions.node_pos`. Selected children add the two induction bounds. Unselected children use nonnegativity for the unused head. A row uses the exact equation `Positions.edge row = Positions.children row.children`. Ordinary node reconstruction consumes its row bound, which is below `1 + Positions.rows edges`. The list theorem is a two-case wrapper.

The existing counts and append laws are in `SourceCurrentAllocatedFiniteOrdinaryValuePositions.lean:24`, lines 29-40, 47, 51, and 58. Its `profile_node` at line 140 and `profile_forest` at line 158 then give these input-only bounds without another execution proof:

```text
calls(node)   <= 1 + A * OccurrenceBounds.edgeCount R A H
calls(forest) <= C * (1 + A * OccurrenceBounds.edgeCount R A H)
```

This counts only the native query after each Force, because every `SharedTargetLeaf.Leaf.apply` contains exactly one such query (`SourceCurrentAllocatedSharedTargetLeaf.lean:37`). A first Force can itself run additional native queries inside its Target. Those requests are charged by the Target/Force budget. They are not extra edit leaf occurrences.

## Keep captured and current profiles separate

Let the captured forest have profile `(Rc, Ac)`, length bound `Cc`, height bound `Hc`, and record path-depth bound `D`. Let the current immutable edit input have profile `(Ri, Ai)` and height bound `Hi`. The generic edit API permits different captured originals and current inputs. Do not identify these profiles until the Class wrapper, whose literal graph captures and edits the same forest (`SourceCurrentAllocatedClassEdits.lean:36`).

The new causal slot invariant is `SharedProfiles.Stored T At Hc before` (`SourceCurrentAllocatedFiniteOrdinarySharedProfiles.lean:28`), where:

```text
T  = SharedForceResources.targetRows record Rc Cc D Hc
At = max Ac 1
Q  = NativeBudgetNumbers.nodeBudget (max T Ri) (max At Ai) (max Hc Hi)
Ro = (max T Ri) * (max T Ri)
Ao = max (max At Ai) 1
```

The root-owned `SharedLeafResources.complete` interface (`SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.lean:83`) uses exactly this separation. A first Force pays for a target from the captured forest. The following query uses both captured-target and current-input height bounds. Its result has profile `(Ro, Ao)`, `NodeNarrow input result`, and height at most `Hi`. Its receipt and slot invariant are at the same actual returned state. This producer is the concrete leaf case to use; a public universal callback/output-profile assumption would leave the caller proof open.

## Exact output-profile induction

For node, children, rows, and list, retain the ordinary physical/semantic receipt and add these structural conclusions:

| Family | Additional conclusion |
| --- | --- |
| node | `NodeShape Ro Ao result` and `NodeNarrow input result` |
| children | `ChildrenShape Ro Ao results`, exact input length, ordered `All₂ NodeNarrow` |
| rows | `RowsShape Ro Ao results`, exact input row length, ordered `All₂ EdgeNarrow` |
| list | the children conclusions; an ignored root leaf only widens the unchanged input profile |

Every family also returns `SharedProfiles.Stored T At Hc after`. Existing full Ready, current inventory admission, availability/residency, field loads, global validity, and semantic Merge coverage must be threaded in their actual state order. Use the existing Effects receipts for these facts; no profile follows merely from NodeNarrow.

At an unselected child, widen its original `(Ri, Ai)` profile to `(Ro, Ao)`. This uses `Ri <= (max T Ri)^2`, including the zero case. At a selected child, apply the node induction hypothesis, then process the unchanged original tail at the returned state. Do not use the returned head profile as the input profile for that tail. At a row, use `children_length` (`SourceCurrentAllocatedSharedEditGraph.lean:83`) to retain the original arity, then actual `OutputConstructors.makeEdge` (`SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.lean:87`) with its original full guard. At an ordinary node, retain the original number of rows and use `OutputConstructors.makeNode` at line 102. That lemma handles canonical filtering and cache hits under the derived physical facts. The recursive case is impossible from the original input profile.

The existing supplied-read narrowing endpoints (`SourceCurrentAllocatedFiniteOrdinaryEdits.lean:244`, lines 256, 268, and 280) supply domain/height facts. They do not currently supply numeric output profiles. The new profile induction must derive those profiles from the same actual leaf receipts or construct them with the concrete leaf producer. If a supplied-read endpoint is wanted without headroom, it needs a ranges-free profile analogue of `FiniteOrdinaryReceiptStructure.target_reads`; do not replace that missing lemma with an assumed result profile. The finite resource endpoint can instead construct each leaf with the derived current prefix headroom.

## Cumulative construction and remaining scope

For the first finite edit resource theorem, use a fixed worst-case leaf cost based on the separate captured and input envelopes. Charge it once per counted input position. Add raw rebuild requests from the existing ordinary node/row occurrence bounds. Construct the selected head first, derive the remaining headroom from its actual Work trace, then construct the original tail. This gives the same source graph with warm tables. It does not require an old range plan quantified over future states. A sharper bound can separately prove at most one target miss per record path from slot retention; every leaf query still pays `Q`.

These are remaining proof obligations, not new completed theorems. No source edit or build was performed for this plan. After the edit producer, the Class wrapper must derive compiler and path-support facts and start fresh slots. The Pass wrapper must update its profile envelope tail-first because each next class captures the preceding returned forest. Require/Scan/local/parent/whole outer cumulative reservations remain open after these steps. Keep the existing conditional class language and asymmetric approximate emptiness contracts. General recursive termination, equality and host resource bounds, runtime demand/publication correspondence, and remaining library/API/Sized contracts are outside this finite ordinary position argument.

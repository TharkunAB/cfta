# Checked edit resource API review

Reviewed: 2026-10-16 21:19 CEST.
Scope: read-only review of existing interfaces. No production file changed. No build ran for this review.

## Result

Construct the exact `EditNode` / `EditChildren` / `EditRows` / `EditList` graph and its indexed strict Reads first. Then call `SourceCurrentAllocatedSharedEditEffects.{node_effects,children_effects,rows_effects,list_effects}`. Each call derives its full physical receipt for that same graph and return. Do not copy the private receipt assembly.

The new construction proof must still derive the stronger profile stores, output profiles, actual constructor Work trace, request bounds, and final supply bounds. The old effects and narrowing endpoints do not derive these new resource fields.

A conservative first bound may charge every reached leaf for a full captured target plus its native query. It does not need a distinct-miss count. Count traversal over the original current input positions and original rows. Do not traverse generated replacement results in the count.

## Existing receipt interfaces

`SourceCurrentAllocatedSharedEditEffects.lean:449-495` exports these exact argument orders. Type, graph, formula, solver, base, and initial inventory indices are inferred.

```text
node_effects reads populated hasLeaf allowed ready available safe valid
  : exists next, NodeReceipt ... next ... input before result after memos final

children_effects reads populated allowed ready available safe valid
  : exists next, ChildrenReceipt ... next ... inputs before results after memos final

rows_effects reads populated allowed ready resident safe valid
  : exists next, RowsReceipt ... next ... edges before results after memos final

list_effects reads populated allowed ready available safe valid
  : exists next, ChildrenReceipt ... next ... inputs before results after memos final
```

The common receipt fields are `.ready`, `.effects`, `.extension`, `.slots`, `.retained`, and `.globals` (`SharedEditEffects.lean:44-85`). These retain the actual returned full Shared state. `.ready` carries the next computed inventory. `.effects` carries the actual heap and equality-operation growth. `.slots` retains old target slots. `.retained` extends the Merge memo. `.globals` supplies validity and unfolding extension for the actual final global bundle, with unchanged query memos. The specialized receipts add result availability/residency and ordered path-domain transport.

The effects endpoints do not require `known`, captured path domains, class coherence, or nontriviality as separate arguments. The supplied leaf Reads already contain full leaf receipts. Construction of those leaf receipts still needs the legitimate captured inputs and class facts.

`SourceCurrentAllocatedFiniteOrdinaryEdits.lean:244-293` accepts the same Reads and initial effects arguments. It then takes `known capturedDomain stored domain`. It derives structural `Shared.Stored after` and `NodeNarrow`, ordered `All₂ NodeNarrow`, or ordered `All₂ EdgeNarrow`. This is domain and height narrowing. It is not a language theorem or a profile-store theorem.

`SourceCurrentAllocatedSharedEditLanguage.lean:271-306` derives language narrowing and conditional preservation from the same Reads. The list endpoint takes `read valid populated allowed ready available safe memoValid`. Preservation also needs accepted captured originals, class satisfaction, and the compiled edit condition. It does not assert unconditional language equality.

`SourceCurrentAllocatedSharedEditComplete.lean:190-240` shows the intended reuse: construct graph and Reads, then call the public effects endpoint. Its own completion premise is an old reached range plan. The new initial-headroom construction must not import that plan as an unexplained premise.

## Minimal constructor and state joins

`SharedEditGraph.advanceHeap` (`SharedEditGraph.lean:27-30`) is the exact constructor join:

```text
SharedState.advance before
  (QueryMemo.advancePhysical before.checked <newHeap, before.checked.operations>)
```

It retains the native result/domain tables, equality operations, Merge memo, and shared slots. It replaces the constructor heap. Leaves may change the equality operations and native tables before this join. Use the current returned prefix state, not the initial state.

`SharedEditEffects.node_physical ready rebuiltRows residentRows` (`:91-108`) derives current Ready, physical Effects, and actual result availability for literal `run (makeNode rebuiltRows)` followed by that join. It needs no closed-row premise.

`SharedEditEffects.edge_physical ready symbol rawGuard children field available` (`:110-133`) derives current Ready, Effects, actual edge residency, and exact returned children for literal `run (makeEdge symbol rawGuard children)`. It keeps the full raw guard. It needs its current `FieldAvailable` witness. It needs no universal conjoin, initial Top, or MkEdge acceptance premise.

Obtain the original row field from `ready.checked.good.fields key edge originalResident`. After child edits, use `field.grows childReceipt.effects.grows`. Construct the row at the actual child-return state. Same-arity rebuild uses raw `makeEdge`; do not invoke MkEdge again. `SharedEditGraph.children_length` (`:93-105`) gives exact child-list length.

For a constructor step, `SourceQueryUnfoldMemo.valid_grows beforeHeap afterHeap semantic keeps currentMemos valid` (`SourceQueryUnfoldMemo.lean:84-91`) derives validity of the same global bundle. Both raw constructors are global-read silent. Their new Reads constructors pass the same bundle through. The complete edit can grow unfolding memos through force calls; do not claim whole-bundle equality across the entire edit.

Use prefix receipt `.effects.keeps.available` to retain untouched original children. Use `InternedEdgeResidency.edge_grows` with `.effects.keeps.growth` to retain original suffix rows. The exact pattern is already present in `SharedEditComplete.lean:121-171`.

`SharedProfiles.physical_stored state physicalAfter stored` (`SharedProfiles.lean:47-54`) retains the stronger native/output/Merge/slot profile certificates through a raw constructor join. `SharedProfiles.Stored.domain` (`:72-75`) supplies the weaker structural store for `FiniteOrdinaryEdits`. Do not replace the strong store by that weaker result when constructing the suffix.

## Construct each raw branch

1. A node-level `.editAt path` calls `SharedLeafResources.complete` at the current state. Its full receipt gives `.leaf receipt.actual` and `NodeReads.leaf receipt` directly.
2. A below-edit of Empty returns Empty, the exact initial state, the initial global bundle, and an empty Work trace.
3. A below-edit of an ordinary node first constructs edits of the original ordered rows. Use the resulting row Reads with `rows_effects` to obtain the actual intermediate Ready and resident returned rows. Run literal `makeNode`, then form `.ordinary rows rfl` and `.ordinary rowReads`.
4. An unselected child retains its literal input value and constructs only the suffix.
5. A selected child constructs its node edit, derives `node_effects`, and then constructs the suffix at that exact returned state and global bundle.
6. A row first constructs edits of its original children. Derive `children_effects`, the grown original field, and `edge_physical`. Construct the row suffix at the literal raw-edge return. Form `.cons children rfl suffix` and `RowsReads.cons childReads suffixReads`.
7. A list-root `.editAt` is ignored. It makes no leaf call. A list-root below-edit constructs `EditChildren entries 0`.

Finite ordinary input profiles exclude Mu, references, and explicit union constructors throughout. Thus the `.recursive` head-exposure branch is impossible in this new producer. No head callback, body-completion oracle, or generic guard law is needed.

## Captured and current envelopes

Keep the captured original profile `R,A,C,D,H` fixed in all recursive calls. The captured forest is `originals` in the fixed `base`; targets always use that forest and the original class. The current input has separate `Ri,Ai,Hi`. Each original descendant uses that same current envelope, with its actual height bounded by `Hi`.

`SharedLeafResources.complete` (`SharedLeafResources.lean:83-120`) takes captured `ChildrenShape R A originals`, length bound C, class-path depth bound D, captured height H, and strong slots bounded by `TargetRows record R C D H`, `max A 1`, H. It separately takes current `NodeShape Ri Ai input` and current height bound Hi.

Its result supplies the full leaf receipt, the same strong captured slot store, actual Work trace, constructor request counts, final capacity, and both final supply bounds. Its output node profile is:

```text
rows  = (max (TargetRows record R C D H) Ri)^2
arity = max (max (max A 1) Ai) 1
height <= Hi
```

The new common edit-output envelope may widen this row bound to include Ri and may widen this arity bound to include Ai. Use `NodeShape.mono` for untouched original values. Do not use a replacement output envelope as the captured slot envelope. The latter remains fixed by the captured forest.

`FiniteOrdinaryFinite.closed state coherent value available domain` (`FiniteOrdinaryFinite.lean:38-53`) derives current cached free names `[]`. `CurrentEditDomains.closed_safe` then derives Safe from actual semantic Ready. This avoids assuming arbitrary cached metadata equals zero. The leaf resource endpoint already derives the needed input closure from its profile and availability.

## Output profiles and ordered lengths

`OutputConstructors.makeEdge symbol guard values heap coherent cached available childrenProfile arityBound` (`OutputConstructors.lean:88-102`) covers misses and coherent cache hits. The actual returned edge has the given ordered children profile.

`OutputConstructors.makeNode edges heap coherent linked resident rowsProfile rowBound` (`:105-124`) covers filtering, canonicalization, and coherent cache hits. `normalized_rows` (`:58-64`) proves the selected row profile and nonincreasing row count.

`children_of_all₂` and `rows_of_all₂` (`:67-85`) collect ordered result profiles and exact list lengths. A small raw `EditRows` length lemma is enough if the producer does not already carry an ordered relation. Alternatively, `rows_effects.transport.length_eq` gives this equality once its Reads exist. One reconstructed raw row corresponds to one original row. Bound the ordinary result's root rows by the original row count, not by the enlarged descendants' row counts.

Height narrowing can be obtained after Reads construction from `FiniteOrdinaryEdits.*`. Its positional `NodeNarrow` relation plus `FiniteOrdinaryNarrow.{forest_height,rows_height}` preserves the original maxima. The raw constructor narrowing helpers `FiniteOrdinaryNarrow.makeEdge/makeNode` are also public (`Narrow.lean:128-155`). None supplies a desired parent language law as an input.

## Conservative static resources

For a first proof, let `L` count reached node-level leaf calls, `N` count ordinary node reconstructions, and `E` count original row reconstructions. Use:

```text
node headroom = N + L * (full captured TargetN + uniform native Q)
edge headroom = E + L * (full captured TargetE + uniform native Q)
```

The uniform Q uses the separate captured target and original current input envelopes. A present slot pays zero Force Work, which is bounded by the full captured target budget. Each leaf still pays for its native query. This bound does not need m distinct misses or a slot-absence invariant.

Count repeated source positions, including repeated IDs. A selected node leaf returns immediately; traversal does not enter the generated target or native result. A below-edit only traverses original row and child positions. Rebuilt row count is the original row count even when `makeNode` later filters rows.

Important count boundary: `Occurrences.node .empty = (0,0)` (`Occurrences.lean:17-20`), but a node-level `.editAt` on Empty still forces its target. Therefore ordinary-node occurrences alone cannot bound L. Use an edit-sensitive leaf counter with `.editAt _ => 1` for every Value, or count all original Value positions including Empty. `EditList.editAt` instead has L=0. Existing ordinary node and row occurrence counts can bound constructor reconstructions.

Append the exact traces in source order. `ConstructorWorkTrace.Trace.work` records each literal makeNode/makeEdge action. `Trace.trans` retains the exact intermediate heap and request concatenation (`ConstructorWorkTrace.lean:17-24`). `Reservations.makeNode_requests` bounds its node requests by 1 and edge requests by 0; `makeEdge_observe` records exactly one edge request (`Reservations.lean:193-216`). Cache hits are still requests. `Trace.next_le` then derives final supplies from these actual requests. Do not define request counts as final-counter differences.

An induction uses initial total headroom and each completed prefix's supply bound to pay for the suffix. It does not need a future Capacity, range plan, completed parent trace, result law, or set of future keys.

## Endpoint and scope

A sufficient new result is an exact raw graph, its strict Reads, strong SharedProfiles.Stored at the same return, ordered result profiles and height narrowing, actual WorkTrace, request bounds, and final capacity. Call the public effects endpoint on those Reads to add the full physical receipt. Call the independent language endpoint for conditional semantic preservation. Finally, `SharedEditWorkerCompletion.{node_complete,children_complete,rows_complete,list_complete,editAll_complete}` derives stable literal six-bound execution for that same graph (`SharedEditWorkerCompletion.lean:171-199`).

This route establishes initial-only constructor resource admission for the finite ordinary edit component. It does not bound equality-interner resources, all host instructions, GHC demand/IntMap evaluation order, general Mu/reference/union recursion, repeated outer passes, or the full implementation. This review identifies no new Haskell behavior defect.

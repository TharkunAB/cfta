# Next checked target fold

Read-only handoff, 2026-10-16 08:43 CEST. No proof source edit or build ran for this note.

## Established input

`SourceCurrentAllocatedMergeOperand.complete` constructs the selected Forest projection, then the allocated merge at that exact returned checked state. Its receipt derives full Ready, inventory At, physical Effects, closed available output, retained original Values, merge Stored, uniform ambient CacheCovers, exact native table/domain retention, merge Extends, and the same projection-plus-merge global receipts. Initial selected ForestClosed is sufficient. Unrelated ordinary siblings can remain open. `of_required` obtains this domain from the actual current Required receipt.

The former initial-Top bridge is closed by the allocated merge graph's actual topRow instruction and its same-cache field proof. A large group derives the Top field at the returned operations. Hits and small groups do not gain a fabricated allocation. The source wrapper uses literal equality with Top, with an unconditional PCS truth theorem. Its concrete `.and []` witness separates that test from `SourceMemoGate.plain`.

## Exact next graph and order

Port the first-seeded `Target` and `Fold` shape from `SourceCurrentMemoDemandTarget.lean:26-45` to the full checked state and explicit initial/final merge Memo. Do not reuse its old Scoped.Step.

- Target `[]` returns EmptyNode with the whole state and merge Memo unchanged.
- Target `seed :: rest` runs Fold with a deferred seed. Fold `[]` projects and merges seed.
- Fold `path :: paths` first projects and merges path. It then runs the recursive Fold on paths at that literal returned checked state and merge Memo. It finally intersects the retained head operand with the returned tail.
- Thus operands are demanded in `rest ++ [seed]` order. For `[A,B,C]`, demand B, then C, then A; intersect C with A; then intersect B with that result. This is `foldr intersect A [B,C]`, not a left fold.

This matches `Equality/Operations.hs:228-230`. Each class captures the forest returned by the tail of the class right fold. Its target excludes the edited path and uses the other paths in ascending order (`:236-244`). Keep that captured forest fixed across the edits within one class.

## Completion and receipts

Use `SourceCurrentAllocatedNativeInventoryState.query_complete` for each actual checked head/tail intersection. The existing `merge-independent-probes.lean` kernel `operand_then_query` already constructs an operand and the next generated query. It derives the new inventory, exact query receipt, closed result, final At, and common-term inclusion without a supplied model-validity, admission, or result-language law.

The range plan must supply only WordRanges for the actual request `requestNode emptyDomain head tail` at the actual recursive tail return. It may quantify over actual operand and recursive graph prefixes. It must not supply future completion, Ready, Fields, final At, or a semantic callback. The recursive finite proof derives these from the initial Ready, At, Values, selected path domains, merge Stored/CacheCovers, and initial global validity.

The head value remains resident through the actual tail Keeps. Each query grows the heap, so transport merge Stored through its derived Keeps. Query calls leave the completed merge Memo contents unchanged. Projection and merge leave native cells unchanged; checked intersections can add cells. Thread the actual returned native tables, domains, equality operations, inventory, and global tables. Do not assert that the whole target leaves native tables or operations unchanged. Inventory At can change to a computed next inventory after each generated query.

Derive the same actual trace's global receipt with `AllocatedNativeGlobalMemos.trace_memos`, between the operand receipts. Retain prior unfolding entries and both query tables. No target operation calls the fourth emptiness memo; retain its exact contents and transport Correct through heap Keeps. Preserve all earlier merge entries and CacheCovers. Conditional target coverage follows by exact native intersection from the independently derived operand inclusions. Merged targets remain an over-approximation; original class constraints remain checked.

## Subsequent shared slots and leaves

Add class-local target slots around the full checked state and the global completed merge Memo. A miss runs the new checked Target and stores its exact historical receipt, captured forest, closed result, and retention. A hit reuses the exact stored value and entire current state, without fabricated target or global calls. Clear only the target slots at a class boundary. Keep merge Memo, native caches/domains, operations, inventory, and global/fourth tables warm across classes.

The leaf then forces its target and performs the actual checked `intersect target input`. Derive the leaf input closed from the selected path domain and structural edit safety. Do not strengthen this to whole-forest closure. Existing compiled-trie transport and path-disjointness proofs can be ported after this leaf contract is established.

## Explicit remaining adapters

The source selection test is literal `edgeConstraint wide == noConstraint` (`Interned/Operations.hs:670-673`). Actual noConstraint CAF allocation and identity correspondence, callback demand timing, HashMap iteration, lazy forcing, and pending memo publication remain runtime adapters. The completed serial graph does not prove those runtime facts. The checked Target/Fold, slots/force/leaf, full class edits, and outer constrained caller remain the next proof work.

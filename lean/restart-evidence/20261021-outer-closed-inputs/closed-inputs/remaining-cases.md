# Partial source review

The partial module has 231 lines. Its SHA-256 is `548336364abf9f81ba0f4b22e4ff35844bfed0c32cd7a82f0611f7a196bc8f25`.
This source is not elaborated. No Lean, Lake, canonical build or runtime example has run. No official source has changed.
Implementation stops before the next complete induction block would cross 250 lines. The public `reached` theorem is not yet declared. No placeholder proof is present.

## Present code

- The public `NodeStored` and `InputsClosed` definitions match the frozen proposal. The public `initial` header matches it and has the direct empty-table proof.
- `begin_stored` uses `lookup_valid` and `demand_spec`. `finish_stored` uses `finish_spec` with closure of the same actual body result. Root accepted this simplification before this review. It does not require a second running-cell ownership proof.
- Ready hits recover the actual captured returned cell. Evaluate starts recover the actual captured evaluating request. The current coherent heap and the same key identify captured and candidate values.
- `edge_closed` uses the actual local call, its existing numeric receipt and the same resource-backed `Written`. `ParentClosed.children` gives returned child closure. The literal numeric `nodes` equality preserves `NodeStored`.
- `modify_closed` covers the unchanged and physical constructor branches.
- Six private predicates retain the actual global `Reached` cut for each completed phase. They do not assume the desired returned closure.

## Remaining cases

1. Keep the original resource packet fixed. At each needed actual global cut, obtain the existing resource/store tuple from `OuterPrefixNativeStores.reached` and the actual edge origins from `OuterResourceWriters.reached`. Do not equate independent existential inventories or copy either induction.
2. Prove the six completed predicates by strong induction on actual outer fuel. Node demand evaluates the same captured request or uses the actual ready cell. The body result closure supplies `finish_stored` at the literal finish handle.
3. Body cases: Empty and union return unchanged values; reference has no successful return; resident Mu reconstruction uses existing `cleanup_free`; ordinary bodies derive original row closure, recurse through rows and apply `modify_closed`.
4. Rows compose the actual Parent edge, descendants and suffix. Descendants use the literal inherited-prefix state, child return and exact `makeEdge_children`. Children either erase to Empty values or enter the actual indexed walk. Walk composes the descended node and suffix with their actual global cuts.
5. Prove the eight-case actual `Reached` induction. The completed predicates handle `rows_tail` and `walk_tail`. Other branches derive captured closure, select a closed row or child, or retain the literal list and node table. Add the exact frozen public `reached` header.

## Scope gate

A straightforward remainder may need about 190–230 lines, giving about 421–461 total lines. This is a scope risk against the reviewed 420-line ceiling. No permission to exceed that ceiling is inferred.
Before further implementation, root and the independent reviewer must read this complete partial source and approve a concrete reduction or a bounded remainder. In particular, the six repeated private predicate declarations and resource extraction sites must stay local; do not add a generic cache or execution framework to reduce the line count.
No compiler command is authorized by this partial review cue. The public premises and four-head scope remain unchanged.

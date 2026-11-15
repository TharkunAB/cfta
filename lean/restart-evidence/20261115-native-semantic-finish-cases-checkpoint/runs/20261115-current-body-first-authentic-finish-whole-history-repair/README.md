# Actual source B/U result at a past producer finish

Status: UNCOMPILED. Root must run the strict private check and public gates.
This packet has no theorem credit yet.

The public theorem is
`SourceCurrentAllocatedNativeAuthenticBodyFirstOuterFinish.body_first_outer_finish_of_past_body_first_key_law`.
It proves that the actual source B/U producer returns the full original stored U.
The parent cell is evaluating at its actual `finishNode` instruction.
The input includes the original source, build, full U metadata, and full authentic P entry.
The result retains the original body, depth, and ordinary metadata.

## Fixed trace and past cache law

The complete fixed trace T ends at `reader` after `wholeCount` steps.
A separate prefix ends at the older `beforeFinish` after `finishCount` steps.
The finish instruction has room inside T: `finishCount + 1 ≤ wholeCount ≤ fuel`.
The authentic U/P or P/U entry may occur after that older finish.

The only semantic induction input is the projected existing
`Returned (BodyFirstKeyQueryGlobalLaws.NodeResult ...)` law at `beforeFinish`.
Root can project this law from the authentic context's `BodyFirstOuter.NodeResult`
inside its stronger past history law. The theorem does not consume a child result
law or a future cache law. It does not instantiate a whole-history theorem.

The `bodyId` identity equation is the source body's existing identity fact.
The source classifier witness supplies the same identity. The proof aligns them.
It does not reconstruct an entry pattern from a numeric identity.

## Proof steps

1. Use the complete T to obtain physical facts and source heap growth at `reader`.
2. Split T at the authentic entry. The actual entry and its suffix preserve P at
   `reader`. Neither P availability nor entry growth is required at the older
   producer.
3. Apply the existing source qualifier at `reader` with the actual entry cache.
   Derive B/U freshness and its `rightMu` selection at the actual incoming key.
4. Use `actual_node_query_dispatch_from_initial_query_finish` to obtain the
   actual query prefix, captured continuation, dispatch step, and raw body trace.
5. Split the actual Mu body into the current-cache entry, the B/B child trace,
   and the optional binder trace. Preserve the original raw child count.
6. Use `keyed_child_law_at_node_finish` on the older finish prefix. It identifies
   the exact B/B returned cell and retains it to this same `beforeFinish`.
   The projected past law supplies its coherent product shape.
7. Derive the child endpoint's physical facts, source growth, and availability
   from the original root plans and actual prefix. Apply the existing coherent
   reclosure theorem at that endpoint.
8. The observed optional binder trace returns full U in one actual step and
   preserves the complete child endpoint, including native and operation state.
   The public conclusion is the parent value equality needed by the finish rule.

The child query starts after `queryUsed + 2` original steps: one memo dispatch
and one actual Mu entry. Its raw `childCount` is unchanged. No observation budget
is substituted for an induction budget. No instruction is inserted.

## Preserved and remaining scope

This is one source B/U auxiliary finish case. Root must still assemble the full
stronger node/edge history induction, including the other auxiliary families.
The full native C/M target, both operand orders, all original P heights, all warm
cache branches, all outcomes, source worker admission, the joint completion goal,
and Haskell correspondence remain open until their own proofs are complete.
A parent ready hit remains covered by the past law at its exact original request;
this theorem handles an actual evaluating parent body.

There is no Haskell change or new Haskell finding in this packet.
No compiler, live source, Git, board, or /tmp operation was run by this agent.

## Scope repair

The earlier packet `20261115-current-body-first-authentic-finish-draft` is preserved.
Its header SHA starts `99fce976`. It ended T at `beforeFinish`, so it could not cover
an authentic entry after that finish. It has no target credit.
The new header separates the complete T and older producer prefix.
`HEADER-SCOPE-DIFF.patch` records every declaration change.
The new complete header and declaration are frozen before compilation.
The three copied original scope files are byte-exact.

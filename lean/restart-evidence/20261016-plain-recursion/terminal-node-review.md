# Independent review of current plain node recursion

Read-only review: 2026-10-16 15:46 CEST.
Reviewed Node SHA256:
`58ae7c5b0f9b8f2d38de7502f5cbc510a8ca7f4181b853407b127b2040668e4c`.
All reviewed source hashes are in `terminal-node-reviewed-hashes.json`.
No proof source was changed and no canonical build was run by this review.

No material defect was found in the inspected source.

## Induction and actual states

`PartialPlainNode.finite:114` derives Below by strong induction on the
independent node rank. Its public hypotheses contain no successful worker
observation, completed graph, recursive callback, or future range plan.
The call to step uses the already-derived smaller-rank Below. The final
worker bounds come from the constructed actual NodeCall graph.

`step:71` excludes busy and absent starts with the active-owner invariant.
A ready hit returns its exact stored result and retained context. An
actual evaluating start derives the running Context and exact owner.
Physical resident-key equality identifies the owner's complete input with
the candidate input. Region and rank therefore transfer to that owner.
The current evaluating owner remains above rank minus one. The proof does
not require recursive Idle while that owner is published.

`body:33` constructs terminal branches from the new terminal completion
endpoint. Mu uses initial filtered probes and actual reconstruction, not
an assumed body return. An ordinary body constructs the ordered actual
Rows graph. It then applies current Actual correctness to that constructed
graph and its derived Checks. This use is not a completion premise.

`PartialPlainRows.rows:64` uses the current edge-call endpoint. Its warm
hits use the Stored three-way certificate at the actual owner's complete
value. Live calls derive current LocalPlain ranges and actual parent
construction. The resulting Shape supplies returned child Regions and
height bounds. Suffix rows retain original resident inputs through actual
physical effects.

`PartialPlainChildren.walk:37` calls Below only on strictly smaller actual
node requests. Indexed descent uses the current returned operation cache.
Completed node and edge graphs restore the original active-owner bound
through reverse ActiveFrames before the next sibling. This restoration is
not inferred from forward protected-frame retention alone. List recursion
uses literal list length. Every prefix threads its computed inventory and
global bundle into the next Context.

## Source and boundaries

The source stops at Empty, Mu, and explicit union at Equality/Operations.hs
84-86. It processes an ordinary row's parent reduction before the returned
edge's descendants at lines 87-96. The inspected graph follows this order.
The returned parent edge has original children, erased children, or the
singleton Empty sentinel. No unchanged-arity claim is used for that edge.
The descendant raw rebuilding stage retains the separately proved slot
length, as required by the existing actual graph.

The proof covers one pass in the structural Region. Mu and explicit union
are opaque Region terminals. Mu cleanup may expose an ordinary result, so
the proof does not assert returned-node Region or recurse into that result.
The edge-result certificate is attached before descendant processing, as in
the separate source edge memo. Arbitrary semantic EdgeLaw plus a height
bound would not replace that certificate.

The initial warm Context, Stored edge-domain certificate, available input,
ready inherited payload, and active-owner rank condition remain explicit.
Cold construction must discharge those inputs separately. The argument does
not assume a finite carrier of future allocation keys. General constrained
outer completion, repeated passes, GHC forcing/sharing, and host identity
correspondence remain separate.

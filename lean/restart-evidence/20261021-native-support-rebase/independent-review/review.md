# Independent mathematical review: native support rebase

Reviewed at 2026-10-21 03:58 CEST. The reviewer did not author this module. The review ran zero Lean or Lake commands. No source or official evidence changed.

The final 49-line source is `bcd4ae7e4690f4c5ceb661328484d7b84e42a3b1b493bc2a3cfac57333e25ee6`. Its sole public head is `SourceCurrentNativePositiveSupportRebase.rebase`. I read its complete statement and proof, the complete captured-origin and prior joint-rebase modules, the source-scope and input-readback definitions used by these helpers, and the exact `Support`, input and memo-validity definitions. I read the selected full theorem and proof output. I found no material mathematical or scope issue.

## Same captured cells

At candidate lines 16–20, both heap facts, forward physical growth, forward issued extension, captured origins at the old source, and old Support are explicit premises. The native state is identical in the premise and conclusion. The proof does not execute a cache lookup or choose a new request.

At lines 30–34, the node branch supplies the identical `handle`, complete `⟨request, .returned result⟩` cell, and `found` lookup to `origins.nodes` and `supported.1.checked`. At lines 43–47, the edge branch does the same with `origins.edges` and `supported.2.checked`. Thus the old law and the origin concern the same captured request and result, even if a later query would have a different candidate. No cache key equality substitutes for the full cell lookup.

## Correct direction of premise recovery

`SourceCurrentConstrainedCapCheckedJointOrigins.bindings_back` (lines 78–91 in that foundation) recovers old-source annotated bindings from later-source bindings. It does not infer a past fact from arbitrary present availability. The captured scope supplies an old complete original Mu witness and old availability. Growth and issued extension carry that old witness forward. Exact payload readback in `Facts later` identifies it with the later binding witness. The proof then retains the old availability and originality, and transports the later annotation and coverage across that equality. The new module supplies `laterFacts`, not `sourceFacts`, to this readback argument.

`NodeOrigin.inputs_back` (foundation lines 57–62) uses the same origin's original operands and old availability. It retains the new pure free-name coverage. `EdgeOrigin.inputs_back` (lines 64–76) uses the same original resident rows and `Facts source` to recover old availability of each ordered child. It retains the new coverage for each same child. This explains the additional use of `sourceFacts` in the edge branch. These steps recover the old conditional premises; they do not assume the desired result law at the later source.

The finite cap proofs apply to complete immutable operand values. The node result path, edge result guard, child index, child value and child residual path are unchanged. The old support law therefore yields precisely the later law. No source-weight comparison is required for this positional statement. The prior joint rebase uses the same input and binding recovery, with separate weight and result-availability arguments for its stronger classifier law; those extra arguments are not required here.

## Bounds, links and phases

`Support` (main native module lines 50–65) is a pair of `FlatMemoThunk.Valid` predicates. Each key relation is literal `True`. Candidate lines 22 and 35 copy each old `bounded` and `linked` field without changing the state or table. `FlatMemoThunk.CellSpec` requires a result law only for returned cells. The suspended and evaluating cases therefore remain `True` at lines 27 and 40. This does not assert a future returned value or completion.

## Evidence and limits

Selected `rebase-direct-1` has exit code zero, source bytes equal to the final candidate, and a literal empty log. Selected `rebase-public-1` has exit code zero and 527,050 bytes of complete check, theorem/proof and axiom output. The printer uses all eight required settings. The sole theorem has only `propext`, `Classical.choice` and `Quot.sound`. The public type has no generated private name. Both original commands use Lean 4.34.1, all linters, a five-minute cap, effective memory.max/high of 4 GiB, zero swap, and a fresh usage sample above one percent. These are two reused author commands and one reused public pair. This package owns zero proof commands and zero new public or constructed pairs.

The theorem does not derive `Origins.Stored` from Support, Good, or bare growth. It does not prove old joint cache laws, their origins at the later heap, Current, causal publication history, arbitrary new generated-input scope, owner renewal, or native termination. It does not claim `later = state.machine.heap`; its source-indexed law is valid for any supplied later heap with the stated forward and origin premises. Existing origin and joint-law transport endpoints remain separate. There is no event, cache, request or result reselection.

The portable verifier checks all frozen source and evidence snapshots. Its live mode also checks ROOT-relative foundation bytes and the installed candidate, if present. It does not rerun Lean or invoke the original worker commands. Verification receipts remain separate from the manifest to avoid a self-reference.

# Original observed terminal resumption: API and fixture review

Reviewed 2026-10-20 22:18 CEST. No material soundness or receipt-correlation issue was found in the complete 210-line final candidate, SHA256 `8c901e5307c0672b338faee6a3c50da1720e012b44d2802b4aaaa1c29935464c`. This is a source review of the producer and a design review of its possible fixture. No Lean jobs or proof pairs were run or reused. The author controls strict and full-public validation. No new fixture was reviewed.

## Exact producer correlation

SyntaxBound is defined with generic Symbol/Guard before the native aliases (33–35). It therefore uses the same generic structural Syntax size function as the old Terminal definition. The proof carries the old bound directly; it does not reinterpret it under a concrete native SizeOf instance.

The private terminal_resume unpacks the old Terminal once (82–85). All five terminal witnesses, its exact SourceRow and completed build, kind, nonunion property, Context, Reached, generic bound and physical/issued suffix stay in that SAME existential. The node branch cases that exact SourceRow and retains its literal buildEdges/makeNode, canonical output lookup, distinct original source/output Nat indices, full RowCall and full output-row identity (86–90). No selected child is needed, so nullary rows remain covered.

The binder branch calls OriginalBinderResume.resume once for the SAME terminal SourceRow and its existing suffix to the fixed enclosing callback (91–94). The output preserves both actual probes/request, complete selected Mu at terminalAfter and the exact sourceHeap, smart finish, RowAt storedBody of that SAME source row, both forward intervals, Written and Stored. It does not replace the selected stored body with the current callback body. Written and Stored remain separate existential propositions; their hidden events are not equated with one another or the enclosing event by the public API.

of_observed takes the exact completed original build from empty and an Observed whose writer reader is exactly that sourceHeap (97–100). It calls the old observed-terminal theorem once and unpacks its enclosing event/raw callback once outside both row quantifiers (189–196). Stored rows preserve their original full row and source receipt. Actual unfold rows preserve their output support/history, full symbol/guard/arity correspondence, identity-or-actual Calls and SAME originalRow anchor before extending that anchor's terminal (201–208). It does not equate substituted output children with stored source children. There is no reverse growth, History-from-Grows inference, second enclosing writer selection, desired terminal-origin premise, Ready premise or future completion premise.

The frozen plan's same-terminal and generic-size requirements are met. The final annotation-only delta makes sourceIndex/outputIndex explicitly Nat in all three copies of the node arm; no mathematical contract changed.

## Warm binder fixture: what can and cannot be forced

The earlier actual box[nested,outer] example remains useful. Its nested body is the nullary tag17 node; its outer body is union[var0,nested]. To target the outer full Mu with an opaque recovered original Stored writer, one can first classify the finite original Reached binder syntax: its callback expression is nestedBody or outerBody. The actual nullary-node callback shape versus the selected outer stored body (an inner full Mu) can exclude nestedBody. This step does not require uniqueness of the historical occurrence or equality with the manually constructed outer event.

However, this is NOT enough to force the new public producer's binder terminal alternative. The extended terminal fields retain global Reached original[] and a size bound, plus an actual terminal SourceRow and a suffix. They do not state that this terminal is obtained from the enclosing expression by only source-union member steps. An earlier original tag17 node callback is also globally Reached, has that same canonical full row and can have a forward suffix to the later callback return. Its node syntax fits the non-strict bound. Thus the API does not exclude a node terminal solely from the enclosing writer's outerBody shape. This is an interface limitation, not a counterexample to the producer.

My preliminary enclosing-writer classification suggestion was therefore incomplete. A fixture must retain the node-or-binder disjunction unless it derives an additional witness tying the returned terminal to the enclosing callback's union descent. It must not equate an opaque terminal with the earlier fixture's manually chosen member1 binder.

The smallest optional strengthening is to add, inside the SAME terminal existential, a pure union-only source descent certificate: reflexive at the source expression and closed only under selected original Syntax.union members. Derive it during the existing terminal_source induction, which descends unions and stops at node/capture/binder. This is not a supplied origin premise. For outerBody=union[var0,nested], that certificate restricts terminalExpression to var0 or nested; the retained node-or-binder kind eliminates var0 and forces the binder. The certificate must be correlated with the SAME terminal witnesses selected by the actual producer. An independent existential terminal or a second source search is insufficient. No such strengthening is proved in this review or required for the current theorem's soundness.

A smaller honest current fixture can apply the new producer once to a derived Observed and expose its complete disjunction. The existing initial-capture family can independently exercise an ordinary node row and changed Calls. Neither test establishes branch completeness, a strict historical-writer/source inequality, lexical occurrence uniqueness or a global renewal/termination rank.

## Inventory and boundaries

This review pins the final candidate, the frozen next plan, the earlier actual warm fixture source and relevant ROOT foundations. All were read without changing their files. Original build identity, actual callback suffixes and native-reader distinctions remain explicit. No Haskell refinement claim is added.

# Next original-source terminal resumption consumer

Design only. No theorem in this note has been implemented or checked.
Reviewed on 2026-10-20 at 22:06 CEST. No Lean jobs are added.

## Exact scope

The next consumer starts with one actual completed build

    build original [] empty = .done sourceRoot sourceHeap

and one supplied

    Observed original [] empty sourceHeap key entry body depth ordinary current.

The Observed writer reader is the exact completed original build heap. The current observation heap can differ. An arbitrary later writer reader is insufficient: Grows event.after reader cannot be reversed to Grows event.after sourceHeap. A more general consumer would need an explicit suffix for that same selected event. The small proposed consumer keeps the exact sourceHeap form.

It calls OriginalObservedTerminals.of_observed once. Its one enclosing publication event and one raw callback result raw/rawAfter stay outside both the stored-row quantifier and the quantifier over all actual successful unfolds. Every old event, callback, Context, Reached, path, growth, issued and row-mapping field remains unchanged.

For each returned Terminal, the consumer unpacks its five terminal witnesses once. It keeps the same terminal expression, input list, entry heap, raw result and return heap. It adds the node or binder result inside that same existential. It does not pair an old Terminal with an independent existential obtained by a second terminal or publication search.

## Preserve the generic syntax bound

Terminal is defined before the native Symbol and Guard aliases. Its syntax bound uses the SizeOf instances selected in that generic definition. A new native conclusion that writes bare sizeOf again can select different concrete instances. It must not be justified by silently substituting a different size function.

The smallest explicit method is one generic definition, also declared before native aliases:

    def SyntaxBound {Symbol Guard : Type}
        (terminal expression : Syntax Symbol Guard) : Prop :=
      sizeOf terminal <= sizeOf expression

This is a proposed definition, not checked code. It has no new semantic premise and no stronger bound. Its generic parameters match Terminal. A native extended receipt writes SyntaxBound terminalExpression event.expression instead of a newly elaborated native sizeOf expression. The existing bound proof is carried by definitional unfolding of that generic alias. There is no native arithmetic reconstruction, explicit runtime SizeOf override or new decrease theorem.

The rest of the extended receipt copies the existing Terminal conjunction under its same five existential witnesses: SourceRow, actual completed terminal build, node-or-binder syntax, nonunion test, Context, Reached original [], this generic bound, Grows terminalAfter rawAfter and issued extension. Append the branch result to this exact conjunction. Do not retain only an unlinked Terminal proposition beside a second chosen terminal.

No additional generic framework is needed. In particular, a new ancestry hierarchy, parametric continuation calculus, source-rank predicate and a family of transport lemmas are unnecessary for this consumer.

## Proposed sole consumer

The additive module can export one theorem, named of_observed, with the exact source build and Observed inputs above. Its result retains the full current OriginalObservedTerminals.of_observed tuple. Replace each Terminal occurrence by the extended same-witness receipt just described. The small generic SyntaxBound definition is the only proposed additional public definition.

At a stored full row, preserve RowAt body originalRow, RowAt raw originalRow and its exact SourceRow before the terminal receipt. At an actual unfolded literal row, preserve the old full symbol, guard and arity correspondence and the identity-or-actual-ordered-Calls alternative to originalRow. Resume the terminal for originalRow. Do not identify that row's ordered children with the substituted output row's children.

### Node branch

Use the node syntax equality and case the exact terminal SourceRow. Retain its actual source row list, buildEdges equation, makeNode equation, canonical output-row lookup, distinct source and output indices, exact RowCall and call.output = originalRow. This is the actual terminal node call. It needs no selected child, so nullary rows remain covered. It makes no assertion that the source index equals the canonical output index.

The enclosing row can lie below a structurally opaque Mu. SourceRow and RowAt retain that structural case. This node conclusion does not become an epsilon read through Mu.

### Binder branch

Use the binder syntax equality and pass that exact terminal SourceRow, terminalAfter-to-rawAfter suffix and issued extension to OriginalBinderResume.resume. Supply the same enclosing event, raw callback, callback Context, actual raw build and filter from the single of_observed tuple. Its event.after-to-sourceHeap growth and issued extension already target the exact original sourceHeap.

Retain the complete resume result under these same terminal witnesses: actual Depth and ordinary callbacks, exact request, same complete selected Mu payload at terminalAfter and sourceHeap, finish equation, RowAt storedBody originalRow, both terminalAfter-to-sourceHeap intervals, Written original [] empty sourceHeap and Stored for that same key and full payload. Call resume once for this chosen binder terminal. No selected-cell, writer or stored-row ancestry premise is supplied.

The writer inside this new Stored can be earlier than the terminal callback. It can also differ from the enclosing publication. The existing warm-winner fixture is an explicit reason to retain these distinctions. The enclosing event remains fixed across the outer row quantifiers; the selected binder's historical Stored publication stays inside its own branch result. No equality between those publications is inferred.

## Proof method and remaining boundary

First unpack of_observed once. For a stored row, obtain the old row mapping and Terminal once. For an actual successful unfold, keep that actual unfold's old output support and originalRow mapping, then obtain its Terminal once. In each case unpack that Terminal once, carry every field and the generic bound, and case only its node-or-binder syntax equality. The node case inverts its exact SourceRow. The binder case invokes resume with the fixed outer callback receipts. Reassemble the same five witnesses and extended branch conjunction.

This plan has no desired source relation, future successful call, Ready or child observation premise. It does not call terminal again and does not reselect an enclosing publication by a matching key or body. The actual source build and the actual suffix are the provenance inputs.

The bound is only terminal syntax size <= enclosing callback expression size under the same generic function. It gives no strict decrease from a binder requester to an earlier selected writer's expression. Stored fixes that writer and callback for subsequent rows, but it does not close a global renewal rank. The proof does not establish original lexical occurrence uniqueness, general capture ancestry, all Head or prior-native entry intervals, or further residual Mu observation. Strict past native-prefix bounds remain distinct from a future execution or termination rank.

## Validation status

This is an unproved next-step contract. The cited terminal, observed-terminal, actual suffix and binder-resume modules are existing checked dependencies. This note adds no source implementation, Lean attempt, printer pair, fixture, official edit or change to a frozen predecessor package.

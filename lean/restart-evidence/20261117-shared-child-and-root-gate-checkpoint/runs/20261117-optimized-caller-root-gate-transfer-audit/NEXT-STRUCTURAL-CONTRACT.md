# First source-qualified structural preprocessing obligation

Status: OPEN DESIGN CONTRACT. This is not an added global premise and not a proved Lean declaration.

Fix the original accepted Hectare **FirstOrder** lib/query/signed input, its current raw constructor expression, and its SAME literal native build. Execute the actual first public `reducePartially` call on that root. For every Mu reached from its returned root by the endpoint detector's ordinary-child/union-member traversal, derive:

    Annotated (fun guard => SourceMemoGate.plain guard = true)
      (.mu entry body depth ordinary)

The fields must be the actual returned Mu record. Do not require its identity or body to equal the original U: preprocessing may rebuild binders. The proof must derive the plain annotation from the original source and actual operation receipts. It may not assume an output gate, output annotation, inherited semantic cache law, or future plain-Mu provider.

The first operation that needs this source qualification is `reduceEdgeIntersection` / `reduceEqConstraints` in Equality/Operations.hs:156–239. Its selected path edits call native intersection on actual path operands. `requireAll` and `editAll` can expose a Mu's rows. `intersectOpen` can allocate a Mu through `maybeMu` (Interned/Operations.hs:506–508,544). The direct unchanged Mu clause at Equality/Operations.hs:85 does not cover those producers.

The reusable existing source facts are the raw stored-U rows, actual source build availability, and source C/M native result closure with its actual input qualifications. A required new call-site lemma must derive those qualifications from the original row/path selection and inherited constraints. It cannot take the desired postcondition as a resource or cache premise.

After that first cut, extending to the real standard caller still needs:

1. The same structural property across each actual later reduction pass and `withoutRedundantEdges`. The latter can rebuild a Mu body (Interned/Operations.hs:760–769).
2. Actual `refold`/`refoldEdges` transport. Those operations traverse and rebuild Mu bodies through `mapNodes`, then replace observed unfoldings (Interned/Operations.hs:90–100,191–239).
3. For Specftacular, a raw StEcta source-family bridge plus its actual 100-round reduction / type-alternative merge, template compilation and post-compilation reduction. `compileTemplates` preserves opaque annotation roots before its later reduction; that fact does not establish their post-reduction shapes. `mergeTypeAlternatives` skips nested-Mu inputs in `merged`, but its enclosing mapNodes still traverses binder bodies.

The Hectare composed property would remove a caller premise: from original accepted construction and the actual preprocessing execution, conclude the returned root's absence of constrained reachable Mu. The checked 81e3 argument can then be reused at the new endpoint after its plain-Mu facts are DERIVED. No such actual composed execution relation is currently exported in normal Source, so a Lean header parameterized by a new opaque `preprocess` and supplied final invariant would be a vacuous wrapper. No candidate of that form is added.

There is also a faithful route that does not force the transformed gate to be false: retain the worker's already generic checkEmpty and specialize it to the detector of the ACTUAL transformed root. This does not itself transfer the original source's language/model through preprocessing. It does preserve the current caller configuration instead of guessing a Bool.

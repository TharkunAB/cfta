# Duplicate query names and ordinary typing

`SourceSynthesisDuplicateQueryAcceptance.duplicate_query_source_counterexample`
checks one literal first-order library, query, Program, and annotation. The library
has `g : A -> C -> C -> R`. The query has `(x,A), (x,C)` and goal R.
The actual modeled `firstOrderRaw` succeeds at four components and accepts
the exact annotation of `g x x x`. Projection, decoding, and count remain exact.
Independent ordinary typing with last-binding query lookup rejects this Program
at EVERY raw type. A, C, and R are ordinary names. This case does not need a
reserved type-tag collision.

The mechanism preserves both original query rows for unrestricted use. Required
singleton uses resolve the last x binding. An earlier unrestricted x:A fills the
first argument. Two required x:C uses fill the remaining arguments. The decoder
retains the name x at each position.

The public theorem has no assumptions. It describes the exported raw Query
route under ordinary last-binding typing. The separate sibling
`20261112-duplicate-query-runtime` packet reproduces the Haskell behavior with
five controls. No production Haskell change is included.

The strict checker emits an explicit #check and an axiom report for every public
theorem. It checks the exact public declaration list and namespace. Own-source
warnings are errors. `checked.json` pins the source hash. Reproduce under the
existing serial 4 GiB heavy-management cap from the repository root:

```sh
python3 lean/restart-evidence/20261112-duplicate-query-acceptance/check.py
```

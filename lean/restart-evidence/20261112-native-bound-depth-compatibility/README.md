# Actual native bounded copying and a stricter encoding boundary

The bounded-copy operational model uses actual native exposure, ordered child
and row copying, native constructors, and a local signed-depth/identity memo.
It retains native heaps and memos on success and failure. Nine branch laws
cover empty input, raw references, signed depth, cache hits, reader outcomes and
row selection. Existing unresolved faults abstract source exception strings.
The arity law proves the same successful child traversal preserves input length.

Current semantic readiness, root availability and closedness derive ONE reader
cutoff. Every larger cutoff returns the SAME successful result, heap and memo.
Readiness, full cache preservation, original/result availability and closedness,
and availability/closedness of every memo value remain intact. No future read,
completion or copied-graph supplier occurs in the public theorem. This proves
component success in the modeled native algorithm. Exact bounded-language
preservation, source-row/cache realization, machine bounds and full optimized
enumeration completion remain separate work.

The encoding law proves two literal raw types are AliasSafe and encode equally,
but are not ordinary Equivalent. The raw function A->B collides with raw
constructor ->[(->)[],A,B]. Current AliasSafe alone cannot imply reflection.
This is a kernel source-encoding result. It makes no new runtime acceptance
claim. All prior Haskell defect reproductions remain separate and unfixed.

frontier.json pins the affected graph and source hashes. checked.json records
full Audit results. portable-check.json records all source packets and full
compatibility from /tmp. source-audit.md retains source contracts and notes.
All prior Audit bytes remain after the four new imports.

Run under the established serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261112-native-bound-depth-compatibility/check.py
```

No production Haskell or Liquid Haskell behavior changes. Keep the entire
original scope, including all alternatives, pre-cap work, semantic operations,
Word/Int, signed APIs/inverses, order/multiplicity, laziness, Haskell and
training/Table/sampler composition. These are component results.

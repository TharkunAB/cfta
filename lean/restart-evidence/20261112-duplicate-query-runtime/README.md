# Haskell duplicate-query coherence reproduction

The public literal Library has `g : A -> C -> C -> R`, representative g,
sole member g, empty avoid rules, and FirstOrder encoding. It matches the
formal source example. The query has goal R. All tests use four components.

| Query arguments | Literal raw acceptance | Generated Program |
| --- | --- | --- |
| x:A, x:C | True | g x x x |
| x:C | False | none |
| x:C, x:C | False | none |
| x:C, x:A | False | none |
| a:A, c:C | True | g a c c |

Each observation forces raw acceptance and the entire output before a ten-second
timeout. Every case finishes. `expected.txt` contains the exact output.
`source-hashes.json` pins six relevant Haskell sources before and after the run.
The checker uses the project Nix shell with GMP, an offline serial unoptimized
library build, runghc-9.14.1, and a fourmolu format check.

Ordinary last-binding typing gives every x type C in the mixed example.
The first application of g requires A. The separate
`../20261112-duplicate-query-acceptance` packet checks actual source acceptance
and independent rejection at EVERY raw type. No reserved type name is needed.

An external repair must state the query-name contract. Same-name ordinary type
coherence or one consistent lookup rule can address this mismatch. Keep duplicate
token multiplicity if that remains part of the API. Requiring unique names is a
stronger contract. The current public raw route has no established uniqueness
check. Parser and Liquid routes are not tested by this packet. No production
Haskell repair is included.

Reproduce under the existing serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261112-duplicate-query-runtime/check.py
```

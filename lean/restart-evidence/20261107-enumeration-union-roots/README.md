# EnumerationUnionRoots

The fixed-head source union fold derives its final class map. The result supports every transfer-list order with the same membership, including ascending set order and duplicates.

Run `python3 lean/restart-evidence/20261107-enumeration-union-roots/check.py` from the repository root.
Use one capped job at a time. The script builds the actual module in `shell.nix`.
It checks the source and every public theorem axiom set. It removes its temporary report.
No archived build tree or private source snapshot is required.
A cold rebuild was not tested separately.

The native source locations are `cfta/src/Data/CFTA/Enumeration.hs:741-754`
and `cfta/src/Data/CFTA/Internal/UnionFind.hs:99-136`.
The statements use the finite mathematical view of those operations.
They do not establish machine-integer bounds or verified Haskell extraction.
The cache transaction uses a valid incoming flat forest and correct incoming caches.
Its final root map and scan representative witness are derived internally.
It covers successful transaction endpoints. It does not bound failing or intermediate work.
Whole-worker composition, native graph/intersection realization, recursive exactness,
and end-to-end size/count/order/rank guarantees remain separate work.
No Haskell source changed.

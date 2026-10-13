# Ordinary source metadata and recursion filtering

`EqualityLeafProjectionOrdinaryMetadata.ordinary_metadata` derives zero Mu
depth and an empty free-reference list for every coherent available ordinary
record. It follows the complete stored child records and the actual parent
metadata equations. It does not assume metadata correctness from syntax.

`ordinary_fast_path` accounts for the source reference and union checks
before its `numNestedMu == 0 && null freeVars` test.
`represented_forest_fast_path` derives that test for every root of a
represented finite raw occurrence forest. Thus any path starting at an
existing root takes the source immediate false branch in
`nodeMeetsConstrainedMu`. Missing roots and empty forest paths also return
false directly. The recursive-node exclusion filter retains every class in
this ordinary fragment. These metadata also justify the source closed
self-intersection shortcut used by the raw leaf product.

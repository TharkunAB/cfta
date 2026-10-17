# Indexed encoded row execution

The source is `SourceCurrentSubstitutionRowExecution.lean`.
Its SHA256 is `de4f42e7d1f2b423a473c3960f5702277818806c605cf5130dffcdefcd58d2cb`.
All older production sources and evidence directories remain unchanged.

## Result and assumptions

`ChildTrace` records each literal repaired `build (encode context locals child)`
with the same captures and exact before/after heaps. Its two constructors
retain the original child order. `children` derives the trace from the actual
completed encoded `buildMany`. `actual` reconstructs that same computation.
`length` proves exact child count. `indexed` retains the same source/output
position, a prefix trace, the actual child call, and a suffix trace.
These child results require no facts, source availability, result origin,
annotation, or future child callback premise.

`rows_indexed` derives each literal rebuilt row's original occurrence at the
same pre-normalization index. It retains the exact prefix and suffix encoded
row builds, ordered child trace, and actual final `makeEdge` pair. The actual
readback preserves the literal symbol, full guard, ordered child records,
and arity. This theorem requires initial `Facts` and availability of captures.
It derives availability of actual child results from full source execution.
It does not require that the original rows themselves are resident.
Warm edge winners retain exact children through coherent canonical readback.

`node_indexed` handles actual execution of the rebuilt node syntax
`.node (encodeEdges context locals originalRows)`. It retains the actual
row build and `makeNode` pair. A selected normalized node row maps to an
existential rebuilt-row index and therefore an original row index. This
index need not equal the selected normalized index. The map has no
injectivity requirement. Physical normalization can remove or reorder rows.
The theorem handles the rebuilt-node branch, not closed-source variable
capture as a separate origin case.

All encoded child syntax is permitted, including arbitrary binders and
unions. There is no `PreparedWithoutMu`, finite-cap, plain-row, or whole-forest
closure condition. The results verify actual completed computations. They
do not construct completion from arbitrary initial inputs.

## Selected validation

- Strict snapshot `substitution-row-execution-direct-4.source.lean` matches
  production byte for byte. Its all-linters log is empty.
- Canonical attempt 1 passes the single module target in 338 jobs.
- Public attempt 1 checks 9 distinct declarations: 7 handwritten public
  heads and the 2 `ChildTrace` constructors. Every declaration has explicit
  `#check @`, proof printing, and axiom printing.
- Kernel attempt 2 checks one no-premise constructed integration. It builds
  the initial heap and two closed replacement nodes from source. It rebuilds
  an actual encoded row. Both reference children change to different closed
  records, in the specified replacement order. The row keeps its literal
  guard and symbol. The second child retains its original position, actual
  encoded build, complete intermediate heaps, and prefix/suffix child traces.
  The fixture has no supplied future graph, origin, or final-heap premise.
  It tests changed ordered children. It does not test recursive Mu origin.
- Selected public and kernel sources use all eight explicit printer/linter
  options, including `pp.proofs.threshold 254`. They have no diagnostics or
  omissions. The public probes use only the three standard axioms. The
  constructed theorem uses only `propext` and `Quot.sound`.
- Effective selected cgroup limits are MemoryMax = 4294967296,
  MemoryHigh = 4294967296, and MemorySwapMax = 0.

Failed strict attempts 1 through 3 and kernel attempt 1 remain at their
original immutable source and raw log paths. Failed kernel output includes
`sorryAx`; it is excluded from successful proof coverage. Only kernel attempt
2 is selected. The constructed proof uses a private proof and public alias
to keep printed evidence finite.

## Boundary

This module proves literal call and row execution provenance. It does not
replace the child trace with an assumed future child-origin law. The source
plan equivalence module can relate each literal child call to stored execute
at the same heap. Recursive structural origins across Mu and normalized warm
callback results remain separate obligations. This component does not assert
general outer progress, initial whole-library completion, or Haskell defect.

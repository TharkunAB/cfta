# Directional product coverage and exact native union rows

Updated: 2026-10-14 20:06 CEST.
Proofs: `2083dadf`, `5a8034f8`, and `1f2aa0c6`.

## Exact physical union rows

`MergedFreshOrdinaryGraphOrigins` proves exact origin equations for seed
lists, ordinary rows, union members, and actual repaired Mu unfolding.
Origins retain the complete physical edge record. The Mu equation follows
the actual completed stored executor. It does not replace Mu by its empty
ordinary row projection.

`MergedFreshOrdinaryUnionOrigins.union_origins` follows actual flattening,
identity deduplication, singleton return, stored unions, and ordinary merges.
The stored live-row invariant proves that an ordinary merge deletes no
original edge. The result is exact full edge-origin equality in any repaired
graph view. Guards and ordered physical child identities are unchanged.

`SourceRecursiveIntersectionKernel.union_call_origins` derives this equation
through actual ordered successful child calls in one common later machine.
`exposed_origins` connects completed repaired row extraction to the exact
later caller machine. It retains the physical heap and issued history and
leaves the domain cache unchanged.

`native_left_union_origins` and `native_right_union_origins` derive exact
child-call origins from checked native completion at every larger kernel
bound and later valid normalized machine. `native_exposed_origins` derives
the machine facts from actual native evaluation and completed closed row
extraction. `native_left_union_rows` and `native_right_union_rows` identify
actual row membership with successful final-cache member calls and their
repaired origins. Incoming semantic heaps, coverage, checked `WordRanges`,
source availability, output closedness, and the completed read retain their
explicit scope. No product-language or row-shape contract is supplied.

## The stronger exact relation also fails in general

The new untracked witness is `lean/repro/UnionDiagonalRows.hs`. Preserve it
with the two earlier fixtures. Its ranked alphabet has nullary `a`, `b`,
and `c`, and unary `f`, `h`, and `g`. Define:

```
X = {a, b}
Y = {b, c}
A = f(X) | f(Y)
B = mu x. h(x)
U = A | B
```

Actual `intersect U A` returns the identical original `A`. The exposed input
product contains a cross row `f((X,Y))`. Its child language is exactly `{b}`.
The returned rows are `f(X)` and `f(Y)`. Neither retained physical child has
that exact common language. The cross row is live and has a true guard.

`UnionDiagonalRowBoundary.no_related_readback` proves that no relation can
satisfy the general exact `RelatedRows.Readback` at this root. Allowing
multiple representatives does not repair this contract. Exact matching would
force the cross child to have the language of either `X` or `Y`. The two
separating leaves refute both choices. A deleted empty child cannot accept
`b`. `full_root_language` separately proves the complete correct root
language of the explicit graph. This is not a semantic runtime defect.

The source has overlapping ordinary `f` rows. The reproduction calls
`intersect` directly and confirms that both operand roots occur in an
enclosing original row table. It does not record a complete short-circuit
ambiguity scan. The example does not refute an interface restricted to
unambiguous graphs. The general adapter claimed for arbitrary plain graphs
is the boundary established here.

The live table comparison validates guards, ranked arities, closure, all six
source indices, the three reachable output states, and the separate common
child. The Lean result is an unbounded theorem about that explicit graph.
Verified Haskell extraction remains open.

## Separate directional row simulations

`DirectionalRows.Simulation` covers each source row by a target row with
ordered related children and an explicit implication between complete guards.
False guards and related empty children retain exact deletion reasons.
`language_included` proves full finite-term inclusion on arbitrary cyclic
graphs. `language_exact` combines separate forward and reverse simulations.
The two directions need not use the same child relation.

The older exact related-row interface supplies both directional simulations
through `of_related` and `reverse_of_related`. All older theorems remain valid
for their stated premises. General physical derivation of that stronger
interface is refuted by the witness above.

`DirectionalProduct.project_right` derives structural coverage of every
product row by its original right row, including diagonal reuse. The guard
implication is conjunction elimination. `copy_into_right` derives reverse
coverage from literal root-row inclusion and diagonal child copies. It
assumes no language contract. `UnionDiagonalRowCoverage` supplies both
structural simulations for the live witness and proves full exact language.

`directional_callback_eq` and `directional_scan_eq` connect these separate
simulations to the actual minimum-row callback and ordered ambiguity scan.
`SourceCyclicRowsNativeGate.Directional.compile_eq` proves complete compiler
result equality. `compile_finite`, `class_correct`, and `query_inverses`
retain finite distinct guarded node-count classes, decoder order, both rank
laws, valid rank coverage, and exact rejection. The two physical simulations,
related roots, and completed extraction remain explicit premises.

## Next proof target

Derive the separate directional relations through actual optional-binder
stored reconstruction and repaired Mu unfolding. Use the exact domain/body
witnesses from the preceding checkpoint and the complete union origins above.
Allow a redundant product row to be covered by an operand row through child
inclusion. Preserve both directions, full guard implications, child order,
and explicit deletion reasons. Do not assume the whole product language.

Do not try to derive general exact `RelatedRows.Readback`, even with multiple
representatives. Its sufficiency theorem remains useful in narrower scopes.
The full native two-input law remains open. The primary finite-map reference,
solver-decided, and optimized Sized laws remain proved with their explicit
synchronous product route. The optimized interned core stays unchanged.

## Validation and preservation

Pinned Lean 4.34.1 passes all eleven focused modules and the aggregate audit:
1,484 jobs and 43,973 theorem dependency checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. All new completed modules
are imported by `MicroCFTA/Audit.lean`.

Audit: `/tmp/mcfta-directional-union-rows-20261014-audit.log`.
Live witness: `/tmp/mcfta-union-diagonal-row-current-20261014.log`.
Table comparison: `/tmp/mcfta-union-diagonal-row-validation-20261014.log`.
Reproduction uses Nix with GMP and the exact current workspace package ID.
Fourmolu passes for the new untracked fixture. No production Haskell source
or committed test changed. Existing active-package gild and Haskell suite
evidence remains applicable.

Reproduce the retained witness:

```
nix-shell -p gmp --run 'cabal exec -- ghc -O0 -outputdir /tmp/mcfta-union-diagonal-row-current-build -package-id microcfta-0.1.0.0-inplace lean/repro/UnionDiagonalRows.hs -o /tmp/mcfta-union-diagonal-row-current'
nix-shell -p gmp --run 'timeout 30s /tmp/mcfta-union-diagonal-row-current'
```

The snapshot also saves the exact table-comparison script and focused logs.

Snapshot: `/tmp/mcfta-directional-union-rows-checkpoint-20261014-2006/`.
All 1,853 Lean-tree files are saved. All 1,840 previous files remain. Only
audit imports, both coverage ledgers, and the two preceding component notes
changed among those previous files. Earlier proof and marked-draft bytes
remain. All three fixtures, backups, stashes, and worktrees remain. All work
stays local. Weekly allowance is 26 percent; stop at 1 percent or less.

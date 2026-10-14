# Actual ordinary product rows and the general child-identity boundary

Updated: 2026-10-14 19:20 CEST.
Proofs: `2e6fb87a`, `6afdfe00`, and `dac5f26b`.

## Completed physical row proofs

`SourceRecursiveIntersectionRowReplay.walk_pointwise_replay` derives exact
individual replay from actual completed ordered walks. It retains request
order, duplicate occurrences, checked source inputs, and both cache histories.
The child and edge specializations use actual checked recursive calls.

`SourceRecursiveIntersectionOrdinaryProductRows.node_rows_replay` derives
resident ordered rows and exact final-cache replay for every matched source
edge pair. `node_members_replay` retains exactly live returned rows. The
actual full recursive kernel supplies all callback correctness and replay
premises in `execute_node_members`.

`SourceRecursiveIntersectionProductEdgeReadback` derives complete physical
symbols, conjoined guards, and ordered final-cache child calls. A source arity
mismatch has the actual empty-child result and cannot survive normalization.
A dead equal-arity row has an actual child request that returns `EmptyNode`.

`SourceRecursiveIntersectionProductEdgeShape` reads the child map from actual
successful final-cache outcomes. The empty default in `childValue` is unused
on these requests. `edge_renamed_product` identifies the literal synchronous
edge, including its complete guard. `edge_product_rejected` supplies the exact
empty-child `DropReason`. Source guard conjunction retains its explicit
Boolean interpretation law.

`SourceRecursiveIntersectionProductRowView.node_product_members` and
`node_product_rejected` give the complete normalized synchronous row interface
for an actual ordinary parent. No child-language or whole-product-language
contract is assumed. The child map uses the actual current domain and cache.

`SourceRecursiveIntersectionNativeOrdinaryRows.native_ordinary_product_rows`
derives this interface from a completed checked native ordinary call. Native
execution supplies the kernel bound. The result holds at every larger bound
and every later valid physical/domain machine. The original domain, ordered
children, and actual final-cache map remain explicit. Checked `WordRanges`
retain their existing scope.

`SourceRecursiveIntersectionNativeDiagonal` derives exact closed self reuse.
A nonempty source free environment resets before the self shortcut. Both
kernel and checked native execution return the identical input record and
unchanged physical/domain machine. Native memo state remains separate.

## The general literal child-map contract is false

The retained live witness is `lean/repro/NativeProductRowCycle.hs`. Keep it
untracked with the earlier `NestedUnaryTwoAtom.hs` fixture. It uses the current
in-place library in Nix. Its ranked alphabet has nullary `a` and unary `f` and
`g`. Define these source grammars:

```
L = mu x. a | f(a | f(x | a))
R = a | f(L | a)
```

`R` occurs in the actual source graph of `L`. An enclosing node with edges
`g(L)` and `g(R)` retains two overlapping alternatives. Thus the pair can be
queried by a native overlap callback in a finite plain source region.

The literal target rows of `intersect L R` differ from the synchronous input
rows whose children are separately intersected with the closed public
`intersect` function. In the recorded process the actual `f` child has identity
19, while that separate child intersection has identity 20. Identities can
change between processes. Both smart and raw outer Mu constructors reproduce
the mismatch. This refutes general physical derivation of
`SourceCyclicRowsNativeGate.ProductReadback.members` with the public closed
intersection as its single child map.

The witness checks unary terms at depths 0 through 24. All are accepted by the
actual result, and each answer equals the input intersection. These checks
are finite validation. They do not prove complete language correctness.
No semantic counterexample or required runtime repair follows from the
different identities alone. Keep the optimized interned core unchanged.

Reproduce the witness in the current checkout:

```
nix-shell -p gmp --run 'cabal exec -- ghc -O0 -outputdir /tmp/mcfta-product-row-cycle-build -package-id microcfta-0.1.0.0-inplace lean/repro/NativeProductRowCycle.hs -o /tmp/mcfta-product-row-cycle-counterexample'
nix-shell -p gmp --run 'timeout 30s /tmp/mcfta-product-row-cycle-counterexample'
```

The current workspace library also passes an offline Nix build. The reduced
witness reproduces after relinking that library. Logs:
`/tmp/mcfta-product-row-cycle-library-build-20261014.log` and
`/tmp/mcfta-product-row-cycle-counterexample-current-20261014.log`.

The GMP package supplies the link dependency for the current GHC. The package
ID selects the current workspace library. The earlier larger random probe
found the same mismatch, but its one-symbol alphabet mixed arities. The reduced
ranked witness above is the source evidence for this boundary.

## Next proof target

Preserve the existing functional `ProductReadback` theorem for its stated
scope. Do not try to derive its false literal field for general Mu output.
Use a relation between actual physical output records and original input
pairs. More than one physical record can represent one input pair. Derive
this relation from actual domains, ordered child calls, Mu construction and
stored substitution, union normalization, and final repaired row exposure.

The next checkpoint now proves generic finite-term product correctness from
local related rows, diagonal reuse, and explicit deletion reasons. It also
derives actual native ordinary row relations and connects the minimum
callback, complete ambiguity scan, and compiler Sized laws. The observed
finite Mu transcript now has an unbounded language proof and a formal
functional-row obstruction. Read [related product rows](notes-relational-product-rows.md).

The relation must still be derived consistently through actual Mu and union
execution, stored substitution, and repaired row exposure. Do not supply
language equivalence as its premise. Consistent related roots and local row
closure for those cases remain open. Preserve the functional theorem for
its stated scope.

The primary reference, solver-decided, and optimized finite-map Sized laws
remain proved at their recorded source-model boundaries. Their explicit
synchronous product minimum route does not require the false general
functional Mu adapter. Full native two-input language correspondence and
concrete Haskell runtime verification remain open.

## Validation and preservation

The preceding ordinary-row checkpoint passed all focused checks and its audit:
1,463 jobs and 43,854 theorem dependency checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-ordinary-product-rows-20261014-audit.log`.
All seven completed modules are imported by `MicroCFTA/Audit.lean`.

Live witness log: `/tmp/mcfta-product-row-cycle-counterexample-20261014.log`.
The larger probe and its first mismatch remain under
`/tmp/mcfta-physical-product-rows-native*`.
No production Haskell source or committed test changed. Prior Nix and
formatter evidence remains applicable. All work remains local.

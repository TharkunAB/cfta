# Specftacular

[![DOI](https://zenodo.org/badge/471054656.svg)](https://zenodo.org/badge/latestdoi/471054656)

Specftacular discovers equational laws with ECTAs. It is based on
[QuickSpec](https://hackage.haskell.org/package/quickspec).
Import `Specftacular` to construct signatures and discover laws.
Specftacular was called Spectacular before it moved to cfta; the DOI above is that of the original Spectacular.

This package uses the ECTAs of [`cfta`](../cfta/README.md) and builds with
GHC 9.14.1. [`specftacular-ghc`](../specftacular-ghc/README.md) builds signatures
from a GHC session. Both packages are part of this Cabal workspace.

Build and run from the workspace root. Enter `nix-shell` first:

```sh
cabal build specftacular specftacular-ghc -j1
cabal run bench-lists -- 4 1 +RTS -M4G -RTS
cabal test specftacular --test-options='+RTS -M4G -RTS'
```

The benchmark executables take the term size and the search phase as arguments.
The golden test suite compares the discovered laws with `test/golden/`.
`GOLDEN_ACCEPT=1` updates these files.

The package was imported from
[`TharkunAB/specftacular` at `948a246`](https://github.com/TharkunAB/specftacular/tree/948a24694256758e53925d3bd498efe05f668f51).

The environment variable `SPECFTACULAR_TESTS` sets the number of test cases (1000 by default, as in QuickSpec).
Fewer test cases are faster, but they let more false laws through, and the prover builds on each law that it prints.
With 100 test cases, `bench-huge-lists 7 1` prints false laws, and the rules that follow from them hide true laws such as `xs == take x xs ++ drop x xs`.

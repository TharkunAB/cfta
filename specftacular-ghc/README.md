# specftacular-ghc

Build Specftacular signatures from expressions in a GHC session. This package
uses [`cfta-ghc`](../cfta-ghc/README.md) and
[`specftacular`](../specftacular/README.md) from this workspace. It requires
GHC 9.14.

Enter `nix-shell`, then run from the workspace root:

```sh
cabal build specftacular-ghc -j1
cabal run bench-lists-ghc -- 4 1 +RTS -M4G -RTS
```

`Specftacular.GHC.withGhcSignature` gets the types of expressions from GHC.
It compiles the expressions and the required QuickCheck generators in that
session. The benchmark executables take the term size and the search phase
as arguments.

Unconstrained type variables use distinct carriers `A`, `B`, `C`, `D`, and
`Acc`. Phase 1 merges them. Later phases use the shared Specftacular type
instantiation and pruning rules. Constrained variables remain concrete.
GHC resolves generators for the required types, including function types
and types declared in the session. A missing generator produces a warning.

The shared engine adds independent and integer-boundary cases to the random
test schedule. Session values have erased runtime types. Their applications
use the shared annotation checks. `SPECFTACULAR_CHECKED=1` does not add
`Dynamic` checks to these session values.

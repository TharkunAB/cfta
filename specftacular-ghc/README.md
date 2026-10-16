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

`Spectacular.GHC.withGhcSignature` gets the types of expressions from GHC.
It compiles the expressions and the required QuickCheck generators in that
session. The benchmark executables take the term size and the search phase
as arguments.

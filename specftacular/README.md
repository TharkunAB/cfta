# Specftacular

[![DOI](https://zenodo.org/badge/471054656.svg)](https://zenodo.org/badge/latestdoi/471054656)

[Comparison with the ICST 2023 Spectacular artifact](docs/SPECTACULAR_COMPARISON.md)

Specftacular discovers equational laws with ECTAs. It is based on
[QuickSpec](https://hackage.haskell.org/package/quickspec).
Import `Specftacular` to construct signatures and discover laws.
Use `ftacularSpec :: [Sig] -> IO ()` to print the laws of a signature.
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

The flag `--tests N` sets the number of random cases (1000 by default). The
search also uses eight separately seeded random cases and 32 integer-boundary
and list cases. These reject the recorded overflow
and list counterexamples. Testing does not prove a law. A false law can still
affect the rules that prune later terms. `--recheck N` tests each new law
again on N random cases of sizes 1 to 8 and drops a law that one of them
refutes (0 by default).

Use `A`, `B`, `C`, `D`, and `Acc` as abstract type parameters in a signature.
Each constant must be parametric in these types. It must not inspect their
representation or capture class dictionaries for them. Use concrete types
such as `Int` for arithmetic and ordering. Phases 3 and 4 instantiate each
constant separately. `--checked` retains runtime type checks.

Use `--diagnostics phases` to trace phase and size/type buckets. Use
`--diagnostics detailed` to include candidate demands, schema and instance
exploration, tree insertion, and completion. Events use versioned TSV on stderr. They
include the actual phase, monotonic wall time, process CPU time, and sampled
RTS counters. Add `+RTS -T -RTS` to enable the RTS counters.

Begin events contain input counts. Checkpoints contain completed counts.
End and abort events leave those fields empty. Nested intervals include
their children. A candidate demand can perform enumeration, pruning,
eligibility checks, and sorting. Tree insertion includes proofs and all
demanded generation, evaluation, and equality. Detailed mode forces new rules
to WHNF to measure completion. It does not force test values for logging.
Logging is off by default. Diagnostic timings include its overhead.
Use phase-only mode to identify the phase of a timeout. Detailed logging
can change which phase reaches the time limit.

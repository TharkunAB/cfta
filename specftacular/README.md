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

## Comparison with Spectacular

This table gives a general idea of the cost of a search through phase 4.
The [comparison](docs/SPECTACULAR_COMPARISON.md) gives the method, each
phase, the memory, and the differences between the laws. All runs are on
the same host: an AMD Ryzen 9 7950X with 24 logical CPUs for a WSL2 VM.

- Spectacular: the ICST 2023 artifact, with GHC 8.10.7 and a limit of 60
  seconds.
- Specftacular: revision `8c44a0d9b`, with GHC 9.14.1. One core: the
  defaults and a limit of 900 seconds. 12 cores:
  `--parallel-tests 64 --speculate 64` and `+RTS -N12 -qn4 -A64m`, with no
  limit.

QuickSpec 2 does not run on this host in the comparison.

| Signature | Size | Spectacular s | Spectacular laws | Specftacular, one core s | Specftacular, 12 cores s | Specftacular laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists | 7 | > 60 | — | 23.90 | 11.47 | 41 |
| Octonions | 7 | 0.22 | 8 | 1.00 | 0.48 | 15 |
| Regex | 7 | 5.84 | 42 | 51.68 | 34.12 | 60 |
| ListMonad | 7 | 18.04 | 42 | 4.61 | 3.43 | 9 |
| HugeLists | 3 | 0.64 | 33 | 2.54 | 1.43 | 46 |
| HugeLists | 4 | 28.43 | 90 | 8.58 | 5.87 | 122 |
| HugeLists | 5 | > 60 | — | 55.90 | 42.10 | 291 |
| HugeLists | 6 | > 60 | — | 491.05 | 364.06 | 690 |
| HugeLists | 7 | > 60 | — | > 900 | 3392.93 ᵈ | 1413 ᵈ |

`ᵈ`: with `--type-depth 2 --recheck 2000`. Without the depth bound,
phase 3 at size 7 does not finish.

The limits are different, so a timeout of Spectacular does not show how
long it takes. The law counts are not comparable between the two tools:
the generators, the test cases and some definitions differ (for example,
`usort` in HugeLists). A larger count is not a better result, because false
and redundant equations also count. Specftacular tests each law on 1064
cases, and HugeLists 7 tests each new law again on 2000 more.

The flag `--tests N` sets the number of random cases (1000 by default). The
search also uses eight separately seeded random cases, 40 integer-boundary
and list cases, and 16 cases with two-element lists and a predicate that
selects one element. These reject the recorded overflow
and list counterexamples. Testing does not prove a law. A false law can still
affect the rules that prune later terms. `--recheck N` tests each new law
again on N random cases of sizes 1 to 8 and drops a law that one of them
refutes (0 by default).

Use `A`, `B`, `C`, `D`, and `Acc` as abstract type parameters in a signature.
Each constant must be parametric in these types. It must not inspect their
representation or capture class dictionaries for them. Use concrete types
such as `Int` for arithmetic and ordering. Phases 3 and 4 instantiate each
constant separately. `--checked` retains runtime type checks.

Phases 3 and 4 give each type variable of a constant every type that the
signature can build. `--type-depth D` keeps only the types with at most D
levels of constructors and arrows. A small depth makes the large searches
finish, but the search then loses the laws that need a deeper type.

`--function-buckets` gives a bucket to each function type between two small
data types of the signature. Each test case applies the two functions to a
sample of their argument type and compares the results, as QuickSpec
observes a function. The search then finds laws between functions, such as
`take 0 == zipWith f []`.

`--dump-laws` writes each law on stderr, with the type of each subterm.

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

# Spectacular and Specftacular

This comparison reruns the published ICST 2023 Spectacular artifact against
Specftacular. It measures elapsed time, CPU time, allocation, GC, and memory.
It also compares the printed laws. A larger law count does not imply a better
result: false laws and redundant laws both increase the count.

Specftacular does not print a false Boolean-carrier law that the original
prints. It finds general gcd
commutativity and additional Octonion laws. It improves several running
times, but usually uses more memory. It also misses useful polymorphic
list laws that the original finds.

The experiment ran on 2026-10-16. The sources are:

| Input | Revision |
| --- | --- |
| [Published Spectacular artifact](https://zenodo.org/records/7565003) | `00621f4f0f03e5d0afea3c730434a8842e473546` |
| [Specftacular in cfta](https://github.com/TharkunAB/cfta/tree/290e4f7881a8340d9b0a57a049ff025872b28274/specftacular) | `290e4f7881a8340d9b0a57a049ff025872b28274` |
| [Published QuickSpec 2 benchmark artifact](https://zenodo.org/records/7565011) | Version 2.1.5, commit `967151eae493fa08a414386cdfb5ce7072477972` |
| [Extended paper](https://mpg.is/papers/gissurarson2023spectacular-extended.pdf) | Downloaded PDF SHA-256 `44fcc9a6c67a5ddefccb29c37ce721a354b427bc99d6a01dadbb5b9355535882` |

The Spectacular ZIP SHA-256 is
`48ff8dc6671edd9636c3d2c44928aab80fd3c0f92cb56d380ece8a3ae0ca3fa0`.
The QuickSpec ZIP SHA-256 is
`3de3b0cb9c1411f81a329ea3a39b2be92c346bbdc4b5f61718f966ff930c3a91`.
All 63 Haskell source files in the published Spectacular archive stayed
unchanged. The comparison uses its five benchmark programs, not a port of
those programs to the current engine.

## Method

The host is Ubuntu 24.04 under WSL2, with an AMD Ryzen 9 7950X and 24 visible
logical CPUs. The VM reports 94.29 GiB of RAM. Both versions use one RTS
capability, optimized libraries and executables, and separate processes.
The original uses GHC 8.10.7 and QuickCheck 2.14.2. Specftacular uses
GHC 9.14.1 and QuickCheck 2.18.0.0.

Builds ran inside `nix-shell`, through `heavy-management/bin/heavy` and pueue,
with a 16 GiB cap and `-j1`. Benchmark jobs ran serially through pueue and
`heavy-management/bin/capped`. Each job had a verified cgroup limit of
80,000,000,000 bytes, no swap, and `+RTS -N1 -M64G -s -RTS`.
The first measured pair started below a load average of 1. No comparison
build overlapped a benchmark.

The main matrix uses the same signatures, CLI sizes, and cumulative phases
in both versions. It covers all 27 Spectacular configurations in Table I.
The per-process timeout here is 60 seconds. The paper used 3600 seconds.
These are new measurements on a different host, not replacements for the
paper's historical timings. GHC, dependencies, generators, testing, pruning,
and enumeration also differ. The experiment does not isolate the cost of
the automaton implementation.

Original Spectacular runs 100 fresh QuickCheck tests for each comparison.
Specftacular uses 1000 shared test cases by default. The additional
100-test controls change Specftacular's count, but do not reproduce the
original generator or comparison procedure. Small selected cases run three
times. The large matrix contains one observation per cell.

GNU `time` gives the process peak RSS in KiB. The tables convert it to MiB.
RTS maximum residency measures the live heap at GC samples. It is not RSS.
The cgroup peak includes the job's descendants and charged file pages.
For a timeout, a captured-law count is only partial. Buffered stdout can
also hide laws that the process found before termination.

## Results

T means a 60-second timeout. MiB is peak process RSS. A dash means that the run has no final law count.

| Signature | Size | Through phase | Original s | Original MiB | Original laws | Specftacular s | Specftacular MiB | Current laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists | 7 | 2 | 1.00 | 30.3 | 32 | 0.32 | 63.7 | 16 |
| Lists | 7 | 3 | 17.29 | 77.5 | 73 | 2.10 | 173.8 | 54 |
| Lists | 7 | 4 | 58.74 | 151.2 | 93 | 36.76 | 3270.1 | 67 |
| Octonions | 7 | 2 | 0.13 | 21.1 | 8 | 2.85 | 86.7 | 15 |
| Octonions | 7 | 3 | 0.16 | 20.9 | 8 | 2.91 | 87.0 | 15 |
| Octonions | 7 | 4 | 0.22 | 20.1 | 8 | 2.87 | 87.2 | 15 |
| Regex | 7 | 2 | 2.87 | 17.6 | 42 | T | 70.1 | — |
| Regex | 7 | 3 | 4.27 | 17.1 | 42 | T | 70.3 | — |
| Regex | 7 | 4 | 6.01 | 17.6 | 42 | T | 66.3 | — |
| ListMonad | 7 | 2 | 0.23 | 15.3 | 8 | 0.05 | 19.6 | 8 |
| ListMonad | 7 | 3 | 0.45 | 24.0 | 8 | 0.16 | 32.0 | 8 |
| ListMonad | 7 | 4 | 18.18 | 209.3 | 42 | 1.49 | 166.7 | 24 |
| HugeLists | 3 | 2 | 0.07 | 11.5 | 22 | 0.08 | 36.7 | 20 |
| HugeLists | 3 | 3 | 0.17 | 16.9 | 27 | 0.13 | 58.8 | 22 |
| HugeLists | 3 | 4 | 0.89 | 28.4 | 33 | 0.27 | 59.7 | 42 |
| HugeLists | 4 | 2 | 0.18 | 14.4 | 37 | 0.17 | 56.3 | 32 |
| HugeLists | 4 | 3 | 1.42 | 36.2 | 68 | 0.40 | 90.6 | 38 |
| HugeLists | 4 | 4 | 27.87 | 122.4 | 90 | 3.23 | 205.6 | 84 |
| HugeLists | 5 | 2 | 0.85 | 25.1 | 66 | 0.50 | 93.1 | 58 |
| HugeLists | 5 | 3 | 26.23 | 105.7 | 144 | T | 149.5 | — |
| HugeLists | 5 | 4 | T | 165.5 | — | T | 149.6 | — |
| HugeLists | 6 | 2 | 6.61 | 43.9 | 99 | 1.94 | 259.6 | 78 |
| HugeLists | 6 | 3 | T | 304.7 | — | T | 259.4 | — |
| HugeLists | 6 | 4 | T | 308.3 | — | T | 259.4 | — |
| HugeLists | 7 | 2 | T | 51.1 | — | 13.65 | 910.6 | 127 |
| HugeLists | 7 | 3 | T | 55.5 | — | T | 910.4 | — |
| HugeLists | 7 | 4 | T | 48.4 | — | T | 910.4 | — |

A separate original HugeLists size-7 phase-2 run had a 120-second limit.
It completed in 63.37 seconds, with 66.1 MiB peak RSS and 181 laws.
Table I reports 186 laws for that case. The original size-5 phase-4 Lists
repeats produce 35 laws here, while Figure 7 shows 20. Several other
historical counts agree, including Lists 7 at 32, 73, and 93 laws.
The artifact rerun does not reproduce every historical output exactly.

Selected completed runs show the allocation and GC costs:

| Signature, size, phase | Original allocation GiB | Current allocation GiB | Original heap MiB | Current heap MiB | Original GC s | Current GC s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists, 7, P2 | 4.256 | 1.129 | 11.02 | 23.29 | 0.213 | 0.087 |
| Lists, 7, P4 | 239.298 | 129.568 | 50.81 | 1447.68 | 17.473 | 9.207 |
| Octonions, 7, P2 | 0.423 | 4.641 | 11.92 | 33.86 | 0.024 | 0.121 |
| ListMonad, 7, P4 | 52.591 | 2.477 | 72.24 | 70.29 | 6.969 | 0.471 |
| HugeLists, 4, P4 | 126.944 | 14.659 | 39.68 | 72.55 | 8.635 | 0.571 |
| HugeLists, 6, P2 | 24.788 | 4.571 | 17.70 | 110.93 | 1.285 | 0.533 |

These allocation totals are cumulative bytes, not simultaneous RAM use.
The heap columns give maximum RTS residency. The GC columns give CPU seconds.

The selected short cases have these median times and observed ranges over three runs:

| Case | Original median s (range) | Current median s (range) | Original laws | Current laws |
| --- | ---: | ---: | ---: | ---: |
| Lists, 5, P1 | 0.08 (0.07–0.08) | 0.07 (0.07–0.10) | 17 | 13 |
| Lists, 5, P4 | 1.83 (1.76–2.00) | 0.67 (0.64–0.68) | 35 | 34 |
| ListMonad, 5, P1 | 0.03 (0.03–0.03) | 0.02 (0.02–0.02) | 4 | 4 |
| Octonions, 7, P2 | 0.13 (0.13–0.13) | 3.06 (2.85–3.44) | 8 | 15 |
| HugeLists, 4, P2 | 0.18 (0.17–0.19) | 0.17 (0.16–0.18) | 37 | 32 |

The GNU timer reports hundredths of a second. Treat differences of a few hundredths in the shortest cases as measurement resolution.
The law files agree byte for byte across all three repetitions of each
listed case, for each engine.

The test-count controls use the current implementation in both columns:

| Case | 100 tests s / laws | 1000 tests s / laws |
| --- | ---: | ---: |
| Lists, 7, P2 | 0.19 / 16 | 0.31 / 16 |
| ListMonad, 7, P2 | 0.03 / 8 | 0.04 / 8 |
| HugeLists, 5, P2 | 0.33 / 58 | 0.56 / 58 |
| HugeLists, 7, P1 | 6.89 / 92 | 12.31 / 118 |
| Regex, 5, P2 | 1.79 / 28 | 14.30 / 28 |

Regex size 7 P2 with 100 tests finishes in 51.37 seconds with 58 laws.
At size 4 P2 with the defaults, the original finishes in 0.34 seconds with
31 laws. Specftacular finishes in 4.26 seconds with 17 laws.

Four selected signatures produce byte-identical law files with checked and untyped evaluation: Lists 7 P2, Lists 5 P4, Octonions 7 P2, and HugeLists 4 P2. This check covers those runs only.

The matrix contains 103 process runs: 88 complete and 15 time-limited. All recorded memory OOM counters are zero. The largest measured cgroup peak is 3.21 GiB.


## Differences in laws

### Boolean carriers give false general laws

The original size-7 Lists phase-2 run prints this law, with variable names
simplified here:

```haskell
map f xs == map f (map f (map f xs))
```

For `f = succ :: Int -> Int` and `xs = [0]`, the two sides are `[1]` and
`[3]`. The law is false for the intended general type. The original carrier
types wrap `Data.Monoid.Any`, which contains a `Bool`. Every total Boolean
endomorphism satisfies `f^3 = f`. More tests over that carrier cannot reject
this equation. A fixed-seed sample of 1000 original carrier values contains
only two distinct values. The current sample contains 61.

Specftacular's corresponding run does not print this law. Its carriers wrap
`Int`. This change removes this particular small-domain identity. It does
not prove that all surviving candidate laws are true.

### Representative instances recover useful laws

With the same nonnegative-integer gcd signature and size 3, the original
prints 22 laws. Specftacular prints six. The current first law is general
commutativity:

```haskell
gcd x y == gcd y x
```

The original prints commutativity only with the constants 1029, 1071, and 21.
It also prints several ground instances of the identity laws. The six current
laws include general commutativity, idempotence, the zero identity, and the
three useful constant reductions. This is an example where fewer printed
laws give a more useful result.

At Octonions size 7, the original prints eight laws in each phase.
Specftacular prints 15. The current output includes flexibility,
`x * (y * x) == (x * y) * x`, and three Moufang forms. The original output
does not print those forms. The saved QuickSpec output also has 15 laws,
but the equations are not the same list. Equal counts do not establish
equivalent discovery results.

The paper already explains this kind of difference. Section IV-A,
“Differences in Discovered Laws”, describes QuickSpec's schema heuristics
and their effect on Octonion laws. A different law basis is not itself an
error. The QuickSpec 2 source tests instances of representative schemas
and orders them by generality. The current engine also uses representative
instances. See [QuickSpec 2's schema layer][qs-schemas].

### The native ListMonad signature has limited function generators

At size 7 through phase 2, the two engines print the same eight equations.
Specftacular's phase-4 output repeats those eight forms at A, B, and C,
for 24 laws. Neither output gives the general bind associativity or
Kleisli associativity equations from the saved QuickSpec output.
The native instance table does not supply an arbitrary generator for
`A -> [B]`. Thus these runs do not test the full function-variable workload
that the QuickSpec example supports. The four signature entries alone do
not establish equal test coverage.

### Later phases still need care

The original size-7 phase-4 Lists output contains
`map f (concat xss) == concat (map (map f) xss)` and
`concat xss ++ concat yss == concat (xss ++ yss)`.
The current output contains no equation that mentions `concat`.
These are useful true laws that this current run does not recover.
The other operations cannot establish a nontrivial law about
an otherwise unconstrained `concat`. This is a discovery regression,
not just a different orientation of the same printed equation.

A separate type probe gives one concrete restriction. With the supplied
`[] :: [A]` and `concat :: [[A]] -> [A]`, `termType` rejects `concat []`.
With `[] :: [[A]]`, it accepts the application. The check reads the types
in the original signature. It permits carrier substitutions, but does not
instantiate `A` with `[A]`. This prevents that valid polymorphic instance
from reaching the tests in a later phase.

Specftacular's Lists size-7 phase-3 output contains 54 laws. Of these, 39
have the form `0 == length ...`. Many are ground consequences of the empty
list identities. One printed equation repeats exactly after law numbers
are removed. Phase 4 also repeats familiar list identities at another
carrier type. Thus the current output is not an independent or minimal
axiom set.

The current rewriter checks typed substitutions and repeated variables.
It also completes rules and rejects equations that its prover can derive.
Those mechanisms do not remove all redundant output across polymorphic
phases. The extra law count in those phases must not be used as a quality
score.

### More tests help, but do not establish correctness

The current HugeLists size-7 phase-1 control prints 92 laws with 100 test
cases and 118 with 1000. The 100-test output contains this false equation,
with `succ 0` written as `1`:

```haskell
length (take 1 (xs ++ ys)) == length (take 1 (zs ++ ys))
```

Set `xs = [0]`, `ys = []`, and `zs = []`. The results are 1 and 0.
The 1000-test output does not contain the equation. It also recovers
`xs == take n xs ++ drop n xs`, which the 100-test output misses.
An admitted false law can therefore reduce later discovery.

The 1000-test output still contains this false equation:

```haskell
take n xs == take n (take (n + n) xs)
```

On this GHC, set `n = maxBound :: Int` and `xs = [0]`. Then `n + n` is -2.
The left side is `[0]`; the right side is `[]`. The default's larger test
set does not cover all integer overflow cases. These outputs remain
candidate laws that need independent checks.

## Saved artifact outputs

The Spectacular release ZIP contains source and benchmark scripts. It has
no saved benchmark result files. The GitHub release has no additional
download assets. The companion QuickSpec ZIP contains 28 saved
`examples/tests/*.output` files.

| Saved example | Numbered laws | File |
| --- | ---: | --- |
| Lists | 25 | [Lists.output][qs-lists-output] |
| ListMonad | 11 | [ListMonad.output][qs-monad-output] |
| Octonions | 15 | [Octonions.output][qs-octonions-output] |

These files are example regression outputs, not complete benchmark logs.
The example test runner fixes `QUICKCHECK_SEED=1234`. The Octonions example
requests only one test and a pruning size of 9. ListMonad limits test size
to 20. The benchmark programs have separate settings and take a term-size
argument. In particular, the saved Lists file's 25 printed laws must not be
substituted for the paper's 28-law QuickSpec benchmark result.
QuickSpec itself was not rerun in this experiment.

QuickSpec 2 supplies an arithmetic background theory. In the published
2.1.5 source, [`arith`][qs-arith] declares `0`, `1`, and `(+)` as background
functions. The [driver][qs-driver] first explores those functions. It retains
their laws for pruning, then explores the full signature. It suppresses laws
that contain only background functions. These are discovered background
laws, not a supplied list of arithmetic axioms. Section 3.6 of the
[QuickSpec 2 paper][qs-paper] explains this procedure.

Spectacular's and Specftacular's `arith` supply only `0` and `1`. This is an
expected difference between the adapted workloads. It affects both which
laws can be expressed and which laws are printed. A missing law with `(+)`
does not establish a discovery failure in this Spectacular workload.
Raw counts also need the background-law policy, not just the function list.
The fork's benchmark prints `length res` from `quickSpecResult`. Its driver
collects background laws in `res` even when it does not print them.
Thus the 25-versus-28 Lists counts can reflect hidden background laws;
the difference alone is not a reproduction failure. The saved file does
not list those hidden laws, so this experiment does not verify their count.
This distinction does not explain the missing `concat` laws, which use
functions present in both signatures.

# Amendments

The following corrections concern the published results and the implementation
that produced them. The code fixes were already present in the measured
Specftacular revision. This comparison adds evidence and documentation.

1. **The example output contains an invalid general law.** Figure 7, law 9,
   gives `f x == f (f (f x))`. Integer successor is a counterexample.
   The published source's Boolean carriers explain this identity. The
   rerun finds the corresponding false equation under `map`.
   Specftacular uses integer carriers and does not print that equation in this run.

2. **Pruning must preserve repeated variables and their types.** The original
   enumeration matcher accepts each `<v>` template hole independently,
   without a typed substitution. Its node-pruning oracle can discard a node when
   only some terms match; the original source itself marks this case as
   too strong. The current matcher records typed substitutions and requires
   repeated variables to match equal subterms. The current search does not
   use that node-pruning oracle. The old pruning is not evidence of complete
   enumeration of valid candidate laws.
   See the [published matcher](https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/src/Data/ECTA/Internal/ECTA/Enumeration.hs#L411)
   and the [current rewriter](../src/Specftacular/Rewriting.hs).

3. **One-variable schemas are insufficient for all variable permutations.**
   The current search tests instances of representative schemas. The gcd
   comparison shows general commutativity that the original run misses.
   The fix also changes the law basis, so raw law counts are not directly
   comparable as counts of independent facts.

4. **Runtime evaluation needs a type check at the boundary.** The original
   uses unqualified type names and unchecked coercions. The current code
   qualifies constructor names, recognizes carrier types explicitly, and
   checks a term's type before evaluation. `SPECFTACULAR_CHECKED=1` also
   checks runtime applications. This is an additional check, not a proof
   of correctness for every signature.
   See the [current type and value checks](../src/Specftacular/Types.hs).

5. **Hash equality is not term equality.** The original stores hashes in
   `seen` and uses hash equality in parts of rewriting. A collision can
   remove a distinct term. The current `HashSet Term` and structural matcher
   check term equality. The current shared test cases also remove fresh-seed
   variation between comparisons. No hash collision was induced in this
   experiment.

6. **The explanation of `usort` needs correction.** Table I attributes the
   `sort == usort` result to missing duplicate test inputs. The Spectacular
   benchmark actually defines a duplicate-preserving quicksort. On `[1,1]`,
   both its `sort` and its `usort` return `[1,1]`. The QuickSpec artifact
   imports a different `usort`, defined with `map head . groupBy ... . sortBy`.
   That function returns `[1]`. The benchmark signatures therefore differ
   in meaning. Specftacular still retains the published Spectacular
   benchmark definition. This report corrects the explanation; it does not
   change that workload or repair the historical cross-tool comparison.

7. **The arithmetic example needs its background context.** QuickSpec 2's
   arithmetic background is intentional. It is not an unexplained discovery
   advantage. Figure 2 nevertheless attributes a law with `(+)` to the
   Spectacular signature in Figure 1, which does not supply `(+)`. That
   specific figure needs a signature or caption correction. The present
   comparison preserves the published Spectacular workload. It does not
   add arithmetic background support to Specftacular.

8. **The test budget affects discovery, not only validation.** The original
   uses 100 tests per comparison. The current default uses 1000 shared test
   cases. In the HugeLists control, that default does not print the false length
   equation above. It restores the take/drop reconstruction law. It does
   not fix the integer overflow counterexample. The larger default is an
   improvement in the tested cases, not a correctness guarantee.

The current implementation also has costs that the paper's conclusions do
not establish. It sorts complete enumerated term lists before testing them,
where the original can prune during enumeration. This can increase memory
substantially. Its later phases remain experimental. The public
`ftacularSpec` entry point runs phase 1; the comparison calls
`experimentalPhases` explicitly.

Regex equality still compares acceptance on a fixed sample of 100 words.
It is not a complete decision procedure for language equivalence. Finite
testing and admitted rewrite laws remain part of the result's trust boundary.

## QuickSpec 2 implementation references

The published QuickSpec 2.1.5 source provides useful references for the
remaining gaps. Its [polymorphism layer][qs-poly] retains original and
specialized types. Its [generator resolution][qs-generators] supports
compositional function generators. Its [term exploration][qs-terms] validates
candidate laws and inserts counterexamples into a sparse decision tree.
These mechanisms are candidates for improving coverage, law quality, and
memory use. A separate implementation change must measure their effects.

## Measurement records

The raw measurements, captured laws, and build records remain local to the
measurement host. The tables above report the results. The source revisions,
compiler versions, test budgets, timeouts, and memory limits appear in the
Method section. For example, the largest Lists case uses arguments
`7 4 +RTS -N1 -M64G -s -RTS` with a 60-second process timeout.
Preserve exit codes when comparing results. A timeout is not a completed
discovery run.

[qs-arith]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal.hs#L423
[qs-driver]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L737
[qs-paper]: https://doi.org/10.1017/S0956796817000090
[qs-schemas]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Schemas.hs#L70
[qs-poly]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Polymorphic.hs#L44
[qs-generators]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L326
[qs-terms]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Terms.hs#L74
[qs-lists-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/Lists.output
[qs-monad-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/ListMonad.output
[qs-octonions-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/Octonions.output

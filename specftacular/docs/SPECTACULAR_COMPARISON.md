# Spectacular and Specftacular

This report compares the published ICST 2023 Spectacular artifact with the
current Specftacular implementation. It reports elapsed time, allocation,
GC, peak RSS, and differences in the discovered laws. A larger law count
does not imply a better result. False and redundant laws increase the count.

Specftacular recovers the general `concat` laws and list-monad laws that the
port previously missed. Native checked execution, native unchecked execution,
and the GHC frontend produce the same laws in the selected controls. Sparse
evaluation reduces retained memory. It costs more allocation because it
regenerates inputs. The machine has other activity, so elapsed times do not
establish a speed improvement. Several current workloads still reach the
time limit where the original artifact completes.

## Sources and method

The runs took place on 2026-10-16.

| Input | Revision |
| --- | --- |
| [Published Spectacular artifact](https://zenodo.org/records/7565003) | `00621f4f0f03e5d0afea3c730434a8842e473546` |
| [Current Specftacular](https://github.com/TharkunAB/cfta/tree/01ab62e05aec3a6888bedd456d949c3f89c8d975/specftacular) | `01ab62e0`; native changes through `7410f1c4`, GHC frontend through `e608bdf0` |
| [Published QuickSpec 2 benchmark artifact](https://zenodo.org/records/7565011) | Version 2.1.5, commit `967151eae493fa08a414386cdfb5ce7072477972` |
| [Extended ICST paper](https://mpg.is/papers/gissurarson2023spectacular-extended.pdf) | PDF SHA-256 `44fcc9a6c67a5ddefccb29c37ce721a354b427bc99d6a01dadbb5b9355535882` |

All 63 Haskell files in the Spectacular archive remain unchanged. Its ZIP
SHA-256 is `48ff8dc6671edd9636c3d2c44928aab80fd3c0f92cb56d380ece8a3ae0ca3fa0`.
The QuickSpec ZIP SHA-256 is
`3de3b0cb9c1411f81a329ea3a39b2be92c346bbdc4b5f61718f966ff930c3a91`.
QuickSpec 2 was not rerun. Its source and saved outputs provide reference
evidence.

The host runs Ubuntu 24.04 under WSL2 on an AMD Ryzen 9 7950X. It exposes
24 logical CPUs and 94.29 GiB of RAM. Spectacular uses GHC 8.10.7 and
QuickCheck 2.14.2. Specftacular uses GHC 9.14.1 and QuickCheck 2.18.0.0.
Both versions use optimized libraries and executables, with one RTS
capability per process.

Current builds and runs use `nix-shell`, `heavy-management`, and pueue.
Recorded benchmark cells run serially. Each current job has a verified
16 GiB cgroup cap, no job swap, and `+RTS -N1 -M6G -s -RTS`. Small controls
use heap caps of 2 to 4 GiB. The earlier original-artifact runs have an
80,000,000,000-byte cgroup cap, no swap, and a 64 GiB heap cap. No reported
process reaches either cap. These runs stay below the requested 80 GB limit.

The matrix uses the 27 configurations from Table I. Each process has a
60-second timeout. The paper used 3600 seconds. A separate current Lists7P4
run has a 180-second timeout. The original-artifact measurements remain the
reference for the unchanged artifact. Every Specftacular matrix result below
comes from the current revision. Machine activity differs between the runs.
Do not interpret elapsed-time ratios as isolated engine speedups.

Spectacular runs 100 fresh QuickCheck tests per comparison. Specftacular
uses 1000 shared random cases, eight separately seeded cases, and 32 directed
integer-boundary and list cases. Compiler versions, generators, validation,
pruning, and enumeration differ. The comparison does not isolate the cost of
the automaton implementation.

GNU `time` reports peak RSS in KiB. The tables convert it to MiB. RTS maximum
residency measures the live heap at GC samples. It is not RSS. Allocation is
cumulative traffic, not simultaneous RAM use. A timeout has no final law
count. Its captured output can also omit buffered laws.

## Results

T means a 60-second timeout. A dash means that the run has no final law
count. HugeLists uses different `usort` definitions: the original preserves
duplicates, while the current benchmark removes them. Its law counts are not
results for identical workloads.

| Signature | Size | Through phase | Original s | Original MiB | Original laws | Specftacular s | Specftacular MiB | Specftacular laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists | 7 | 2 | 1.00 | 30.3 | 32 | 0.50 | 21.7 | 16 |
| Lists | 7 | 3 | 17.29 | 77.5 | 73 | 23.74 | 74.4 | 44 |
| Lists | 7 | 4 | 58.74 | 151.2 | 93 | T | 157.6 | — |
| Octonions | 7 | 2 | 0.13 | 21.1 | 8 | 3.64 | 22.1 | 15 |
| Octonions | 7 | 3 | 0.16 | 20.9 | 8 | 3.55 | 24.3 | 15 |
| Octonions | 7 | 4 | 0.22 | 20.1 | 8 | 3.60 | 24.1 | 15 |
| Regex | 7 | 2 | 2.87 | 17.6 | 42 | T | 17.7 | — |
| Regex | 7 | 3 | 4.27 | 17.1 | 42 | T | 17.8 | — |
| Regex | 7 | 4 | 6.01 | 17.6 | 42 | T | 17.6 | — |
| ListMonad | 7 | 2 | 0.23 | 15.3 | 8 | 3.02 | 36.7 | 11 |
| ListMonad | 7 | 3 | 0.45 | 24.0 | 8 | 3.13 | 36.7 | 11 |
| ListMonad | 7 | 4 | 18.18 | 209.3 | 42 | T | 1194.5 | — |
| HugeLists | 3 | 2 | 0.07 | 11.5 | 22 | 0.10 | 16.5 | 30 |
| HugeLists | 3 | 3 | 0.17 | 16.9 | 27 | 0.21 | 22.4 | 42 |
| HugeLists | 3 | 4 | 0.89 | 28.4 | 33 | 2.56 | 50.4 | 51 |
| HugeLists | 4 | 2 | 0.18 | 14.4 | 37 | 0.45 | 25.2 | 56 |
| HugeLists | 4 | 3 | 1.42 | 36.2 | 68 | 4.51 | 92.1 | 97 |
| HugeLists | 4 | 4 | 27.87 | 122.4 | 90 | 28.60 | 195.9 | 176 |
| HugeLists | 5 | 2 | 0.85 | 25.1 | 66 | 6.25 | 176.7 | 106 |
| HugeLists | 5 | 3 | 26.23 | 105.7 | 144 | T | 309.9 | — |
| HugeLists | 5 | 4 | T | 165.5 | — | T | 309.9 | — |
| HugeLists | 6 | 2 | 6.61 | 43.9 | 99 | 11.65 | 257.7 | 149 |
| HugeLists | 6 | 3 | T | 304.7 | — | T | 385.9 | — |
| HugeLists | 6 | 4 | T | 308.3 | — | T | 386.0 | — |
| HugeLists | 7 | 2 | T | 51.1 | — | T | 452.6 | — |
| HugeLists | 7 | 3 | T | 55.5 | — | T | 453.0 | — |
| HugeLists | 7 | 4 | T | 48.4 | — | T | 452.6 | — |

The current matrix contains 15 completed runs and 12 timeouts.

The extended current Lists7P4 run completes with **63 laws**, **207.7 MiB
peak RSS**, **69.4 MiB maximum residency**, and **667.88 GiB
allocated**. Its observed elapsed time is 116.16 seconds. This is a
completed run with a larger time limit than the matrix cell.

Selected completed runs have these costs:

| Signature, size, phase | Original allocation GiB | Specftacular allocation GiB | Original residency MiB | Specftacular residency MiB | Original GC CPU s | Specftacular GC CPU s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists-7-p2 | 4.256 | 4.034 | 11.02 | 3.22 | 0.213 | 0.040 |
| Octonions-7-p2 | 0.423 | 8.203 | 11.92 | 3.53 | 0.024 | 0.045 |
| HugeLists-4-p4 | 126.944 | 161.465 | 39.68 | 75.11 | 8.635 | 9.282 |
| HugeLists-6-p2 | 24.788 | 69.020 | 17.70 | 102.08 | 1.285 | 1.714 |
| Lists-7-p4, extended current limit | 239.298 | 667.885 | 50.81 | 69.40 | 17.473 | 29.192 |

## Differences in laws

The table compares the completed current controls with the original output
and saved QuickSpec 2 examples. The example settings differ from the matrix.

| Law family | Original Spectacular | Current Specftacular | Saved QuickSpec 2 output |
| --- | --- | --- | --- |
| Map over concat | Present | Present | Present |
| Concat over append | Present | Present | Present |
| Bind associativity with function variables | Absent in native ListMonad runs | Present | Present |
| Kleisli associativity | Absent in native ListMonad runs | Follows pointwise from the printed basis | Printed as a function equation |
| Length of append expressed with `(+)` | Lists signature lacks `(+)` | Lists signature lacks `(+)` | Present with arithmetic background |

### Boolean carriers admit false general laws

The original Lists7P2 run prints this equation, with variable names simplified:

```haskell
map f xs == map f (map f (map f xs))
```

Set `f = succ :: Int -> Int` and `xs = [0]`. The two sides are `[1]` and
`[3]`. The original carrier types wrap `Data.Monoid.Any`, which contains a
`Bool`. Every total Boolean endomorphism satisfies `f^3 = f`. More tests over
that carrier cannot reject this equation. A fixed-seed sample of 1000
original carrier values contains only two distinct values. The integer
carriers in Specftacular give 61 values in the corresponding sample.
The current run does not print the false equation. This does not prove all
surviving laws.

### Polymorphic list laws return

Each constant occurrence now has its own polymorphic type instance. The
checker accepts `concat []` when the signature supplies `[] :: [A]` and the
occurrence uses `[] :: [[A]]`. It rejects inconsistent repeated parameters,
wrong application result types, and changes to generated-variable types.
Native checked execution constructs the specialized runtime type and retains
`Dynamic` application checks.

Rewrite rules share one substitution for term variables and type variables.
Repeated occurrences must agree. Abstract type instances precede concrete
instances during exploration. This suppresses many ground consequences.
QuickSpec 2's [polymorphism layer][qs-poly] provides the design reference.

Lists5P4 produces the same 31 numbered laws in native checked execution,
native unchecked execution, and the GHC frontend. There are no exact
text duplicates after law numbers are removed. The normalized law text has
SHA-256 `fd2bdf51ce4f4e9160d52a8d491b135f0308459417dbd6a837e67070d0d21f6a`.
Both general laws are present:

```haskell
map f (concat xss) == concat (map (map f) xss)
concat xss ++ concat yss == concat (xss ++ yss)
```

The completed size-7 run also contains
`concat (concat xsss) == concat (map concat xsss)`. It has no exact duplicate
law text. These checks do not establish a minimal or independent law basis.

### Higher-order ListMonad coverage improves

The native resolver composes function generators from a `CoArbitrary` domain
and a generated codomain. It supports the `A -> [B]` variables required by
ListMonad. User overrides take priority. Function values do not receive a
fabricated `Eq` instance. Unsupported generator types produce warnings.
See QuickSpec 2's [generator resolution][qs-generators].

Applications such as `f x` can serve as representatives. The size-4 existing
golden now includes general list-monad left identity:

```haskell
return x >>= f == f x
```

At size 6 through phase 4, native checked execution, native unchecked
execution, and GHC each produce the same 21 numbered laws. These include
right identity, the applied Kleisli definition, and general bind
associativity in this form:

```haskell
(xs >>= f) >>= g == xs >>= (f >=> g)
```

QuickSpec 2 uses [function observation][qs-observe] to compare results at
generated arguments. It can print equations between functions. Specftacular
compares their applications and supplies no function equality. Its output
does not print the exact Kleisli associativity equation from the saved output. The applied Kleisli definition and bind associativity
imply that equation pointwise. Different equation bases need a derivability
check; their raw counts do not measure discovery quality.

### HugeLists now uses duplicate-removing `usort`

The current size-4 phase-4 run includes
`usort (xs ++ xs) == usort xs`. The duplicate-removing definition supports
that equation. The published duplicate-preserving definition does not.
The current output keeps `sort` and `usort` distinct. Both native and GHC
probes confirm `usort [1,1] == [1]`. This fixes a benchmark mismatch.
It does not make the two measured HugeLists signatures identical.

### Directed cases reject the recorded false candidates

These two equations are false:

```haskell
take n xs == take n (take (n + n) xs)
length (take 1 (xs ++ ys)) == length (take 1 (zs ++ ys))
```

For the first equation, use `n = maxBound :: Int` and `xs = [0]`. Machine
integer addition gives `n + n == -2`. The sides are `[0]` and `[]`.
For the second, use `xs = [0]`, `ys = []`, and `zs = []`. The lengths are
1 and 0.

The current schedule preserves the original random cases. It adds eight
independent-seed cases and 32 cases that combine integer boundaries with
empty and singleton lists. Both counterexamples occur with 100 and with
1000 random cases. A native checked reduced HugeLists signature still
finds `xs == take n xs ++ drop n xs`. `SPECFTACULAR_TESTS` counts only the
random cases. The total is that count plus 40. These cases fix the recorded
failures. Finite testing can still admit false laws that affect later pruning.

### Representative instances change the equation basis

With the same nonnegative-integer gcd signature and term size 3, the original
prints 22 laws. The current golden prints six. The paper describes
generalizing discovered laws. The current search also tests instances of
new representatives. These six laws include general commutativity,
idempotence, the zero identity, and three constant reductions.
The original gives commutativity only at the supplied constants 1029, 1071,
and 21. Fewer laws give a more general result in this example.

At Octonions size 7 through phase 2, the current run prints 15 laws. The
original prints eight. The saved QuickSpec output has 15. Equal counts do not
establish equivalent laws. Current equations include flexibility and three
Moufang forms. The original output does not print these forms.

The paper already explains this kind of difference. Section IV-A,
“Differences in Discovered Laws”, describes QuickSpec's schema heuristics and
their effect on Octonion laws. A different basis or orientation is not itself
an error. See QuickSpec 2's [schema layer][qs-schemas].

## Memory and allocation

The search rejects already seen, ill-typed, and reducible candidates before
it retains the sort bucket. It checks candidates again as new rewrite rules
become available. It does not restore the original unsafe node pruning.

QuickSpec 2's sparse [decision tree][qs-tree] retains counterexamples that
separate representatives. The current engine follows that design. A leaf
retains a term evaluator. A branch retains one discriminator case and its
values. An apparent equality still checks the complete test schedule.
Test cases store seeds and boundary indexes. Evaluation generates only the
variables used by that term. It does not retain all generated nested lists
and complete result vectors at every representative.

A local control uses the same corrected engine and validation schedule, but
restores shared input maps and retained result vectors. Both variants produce
exactly the same 31 numbered Lists5P4 laws.

| Current Lists5P4 control, 1000 + 40 cases | Peak RSS, MiB | Allocated, GiB |
| --- | ---: | ---: |
| Shared inputs and retained result vectors | 3075.8 | 18.29 |
| Sparse evaluation | 59.6 | 50.32 |
| Sparse evaluation with native runtime checks | 64.4 | 51.08 |

The GHC Lists5P4 control produces the same laws and uses 531.2 MiB peak RSS.
That process includes the compiler and interpreter.

Sparse evaluation trades allocation for lower retained memory. On the small
corrected Lists4P1 control, retained vectors use 366,964,713 instructions and
allocate 93,605,016 bytes. Sparse evaluation uses 536,859,602 instructions and
allocates 245,073,984 bytes. The increases are 46.3% and 161.8%. They exceed
the repository's 5% cost budget. The measured implementation experiments
support the decision to retain sparse evaluation for its lower peak memory.
An experimental scalar cache saved less than 1% of full-size allocation and
retained substantially more memory. That cache was removed. A cache with an
explicit memory budget remains possible work. These figures do not establish
a speed improvement.

## GHC frontend

`specftacular-ghc` shares the type checks, rewrite rules, validation schedule,
and sparse evaluator. It assigns distinct carriers to unconstrained type
variables in binder order. Variables that occur in constraints remain
concrete. Container class variables use lists. Other constrained variables
use `Int`. An independent `HasCallStack` predicate does not prevent an
unrelated variable from remaining abstract.

GHC resolves generators for required types. These include functions whose
custom domains have `CoArbitrary` instances declared in the session.
A signature function can have at most five unconstrained type variables.
Generated source still needs unambiguous constructor names in the session.
These probes do not cover qualified-only imports or constructor-name collisions.
Focused probes cover distinct carriers, ordinary and nested class
constraints, `HasCallStack`, custom function generation, and `usort`.
The native and GHC `usort` probes both remove duplicates.

Session values have erased runtime types. Shared annotation checks apply.
`SPECFTACULAR_CHECKED=1` does not add `Dynamic` application checks to those
session values. Native checked execution and GHC session execution have
different runtime checking boundaries.

## Saved QuickSpec 2 outputs and arithmetic context

The Spectacular ZIP has source and benchmark scripts, but no saved benchmark
result files. Its GitHub release has no additional assets. The QuickSpec ZIP
contains 28 `examples/tests/*.output` files.

| Saved example | Numbered laws | File |
| --- | ---: | --- |
| Lists | 25 | [Lists.output][qs-lists-output] |
| ListMonad | 11 | [ListMonad.output][qs-monad-output] |
| Octonions | 15 | [Octonions.output][qs-octonions-output] |

These files are example regression outputs. They are not complete benchmark
logs. The example runner fixes `QUICKCHECK_SEED=1234`. The Octonions example
requests one test and pruning size 9. ListMonad limits test size to 20.
The benchmark programs use separate settings.

QuickSpec 2's [`arith`][qs-arith] supplies `0`, `1`, and `(+)` as background
functions. Its [driver][qs-driver] first explores them. It retains their laws
for pruning and suppresses output about only background functions. These
are discovered laws, not a fixed list of arithmetic axioms. Section 3.6 of
the [QuickSpec 2 paper][qs-paper] explains the procedure.

Spectacular's and Specftacular's adapted `arith` supply only `0` and `1`.
A missing equation with `(+)` does not establish a discovery regression in
that workload. The fork's benchmark counts `length res` from `quickSpecResult`.
Its driver includes hidden background laws in that result. Thus 25 printed
Lists laws versus the paper's 28 benchmark laws can be an accounting
difference. The saved file does not verify the hidden-law count. Compare
foreground functions, background functions, generators, test settings, and
count policy before attributing such differences to the engine.

# Amendments

These corrections distinguish problems in the published artifact and paper
from regressions in the port. The current implementation fixes the code
problems described below. It does not change the published artifact or
retroactively repair the historical cross-tool comparison.

1. **The example includes an invalid general law.** Figure 7, law 9, gives
   `f x == f (f (f x))`. Integer successor is a counterexample. The published
   Boolean carriers explain the identity. Current integer carriers reject
   that identity in the measured workloads.

2. **Pruning must preserve repeated variables and types.** The published
   enumeration matcher accepts each template hole independently. Its node
   oracle can discard a node when only some terms match. The source marks
   that case as too strong. Current structural matching records shared term
   and type substitutions. Repeated variables must match equal subterms.
   Current search does not use that node oracle. See the
   [published matcher][original-matcher] and [current rewriter](../src/Specftacular/Rewriting.hs).

3. **Schemas need representative instances.** The paper describes generalizing
   discovered laws. The current search also tests variable permutations of
   new representative schemas. This recovers general gcd commutativity that the original misses. The fix changes the equation
   basis. Raw law counts are not counts of independent facts.

4. **Type checking must include each polymorphic occurrence.** The original
   uses unqualified names and unchecked coercions. The port also had a
   restriction that rejected valid nested list instances. The current code
   qualifies type constructors, checks occurrences and applications, and
   preserves specialized native `Dynamic` types. Generated variables remain
   rigid. GHC session values retain erased runtime types. See the
   [type checks](../src/Specftacular/Types.hs). Signature constants must be
   parametric in `A` to `Acc`. They must not inspect their representation or
   capture class dictionaries. Use concrete types for arithmetic and ordering.

5. **Hash equality is insufficient for term identity.** The original uses
   hashes in `seen` and in parts of rewriting. A collision can remove a
   distinct term. Current term sets and matching use structural equality.
   This experiment did not induce a collision.

6. **The `usort` explanation describes a different function.** Table I
   attributes `sort == usort` to missing duplicate inputs. The published
   Spectacular function preserves duplicates. Both functions return `[1,1]`
   on `[1,1]`. QuickSpec's `usort` removes duplicates and returns `[1]`.
   Current native and GHC benchmarks now remove duplicates. The original
   comparison used workloads with different meanings.

7. **The arithmetic example needs its background context.** QuickSpec 2's
   arithmetic background is intentional. Figure 2 nevertheless attributes
   an equation with `(+)` to Figure 1's Spectacular signature, which does not
   supply `(+)`. The figure needs a signature or caption correction.
   This does not justify removing QuickSpec's background theory.

8. **Random test counts do not establish validity.** More random tests alone
   do not guarantee coverage of machine integer overflow or list boundaries.
   Current directed cases reject both recorded counterexamples. Neither
   these cases nor the larger random budget prove the surviving laws.

## Limits and remaining work

Phases 2 to 4 remain experimental. `ftacularSpec` runs phase 1. This report
calls `experimentalPhases` for later phases. Rewrite completion remains
conservative for unresolved type patterns. The output is not proved minimal
or complete.

A partial representative can block later candidates after an equality
exception. The sparse evaluator does not fix partial-term discovery.
Further work can study QuickSpec 2's observational results and totality
checks without changing custom non-strict equality behavior.

Regex equality compares acceptance on 100 fixed words, with seed 12345 and
size 10. The current benchmark prints that policy. It remains sampled
observation, not exact regular-language equivalence.

The artifact rerun does not explain every historical law count. For example,
the original size-7 phase-2 HugeLists run with a 120-second limit gives 181
laws, while Table I gives 186. Different saved examples and benchmark
settings must not be treated as the same experiment.

Strict GHC builds pass for both packages and their benchmark executables.
Existing golden tests pass in both native modes. Fourmolu and cabal-gild
checks apply. Raw measurements, CSVs, source checkouts, and local task notes
remain outside this package. This report contains the results and the
source references needed to interpret them.

[original-matcher]: https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/src/Data/ECTA/Internal/ECTA/Enumeration.hs#L411
[qs-arith]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal.hs#L423
[qs-driver]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L737
[qs-paper]: https://doi.org/10.1017/S0956796817000090
[qs-schemas]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Schemas.hs#L70
[qs-poly]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Polymorphic.hs#L44
[qs-generators]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L326
[qs-tree]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Testing/DecisionTree.hs#L42
[qs-lists-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/Lists.output
[qs-monad-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/ListMonad.output
[qs-octonions-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/Octonions.output

[qs-observe]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L181

# Spectacular and Specftacular

This report compares the published ICST 2023 Spectacular artifact with the
current Specftacular implementation. It reports elapsed time, allocation,
GC, peak RSS, and differences in the discovered laws. A larger law count
does not imply a better result. False and redundant laws increase the count.

Specftacular recovers the general `concat` laws and list-monad laws that the
port previously missed. Native checked execution, native unchecked execution,
and the GHC frontend produce the same laws in the selected controls. Sparse
evaluation reduces retained memory. It regenerates inputs when needed.
Completion now rejects impossible matches before comparing their types
and reuses normal forms while the rules stay fixed. CFTA checks mandatory
node pairs once during structural subsumption. Specftacular validates stronger
equation schemes before it adds their rules. Rule orientation now remains
valid across type substitutions. Critical-pair batches share their incoming
terms. Completion preserves generic critical pairs across type instances.
Directed inputs reject the recorded integer-boundary counterexamples.
The fresh matrix completes 21 of 27 configurations, including HugeLists
size 5 through phase 3.
Six HugeLists configurations still reach the limit.
The machine has other activity. Elapsed time alone does not isolate engine
speed. The controls below record both savings and regressions.

## Sources and method

The runs took place on 2026-10-17.

| Input | Revision |
| --- | --- |
| [Published Spectacular artifact](https://zenodo.org/records/7565003) | `00621f4f0f03e5d0afea3c730434a8842e473546` |
| [Current Specftacular](https://github.com/TharkunAB/cfta/tree/102965d3bbffc564b79cb718b73b9f589f95f2ce/specftacular) | `102965d3` |
| [Profiled predecessor][diagnostic-source] | `9be187a0` |
| [Published QuickSpec 2 benchmark artifact](https://zenodo.org/records/7565011) | Version 2.1.5, commit `967151eae493fa08a414386cdfb5ce7072477972` |
| [Extended ICST paper](https://mpg.is/papers/gissurarson2023spectacular-extended.pdf) | PDF SHA-256 `44fcc9a6c67a5ddefccb29c37ce721a354b427bc99d6a01dadbb5b9355535882` |

All 63 Haskell files in the Spectacular archive remain unchanged. Its ZIP
SHA-256 is `48ff8dc6671edd9636c3d2c44928aab80fd3c0f92cb56d380ece8a3ae0ca3fa0`.
The QuickSpec ZIP SHA-256 is
`3de3b0cb9c1411f81a329ea3a39b2be92c346bbdc4b5f61718f966ff930c3a91`.
QuickSpec 2 was not rerun. Its source and saved outputs provide reference
evidence.

The selected runtime is `102965d3`. It includes type-stable orientation,
shared critical-pair inputs, type-uniform completion, and the extended
boundary inputs. The GHC frontend uses the same rewriter and retains
generalized logical carrier resolution. The current columns below come
from a fresh complete matrix of that runtime.
The profiling sections identify each measured source state. Their sampled
percentages do not describe the selected runtime.

The host runs Ubuntu 24.04 under WSL2 on an AMD Ryzen 9 7950X. It exposes
24 logical CPUs and 94.29 GiB of RAM. Spectacular uses GHC 8.10.7 and
QuickCheck 2.14.2. Specftacular uses GHC 9.14.1 and QuickCheck 2.18.0.0.
The runs use separate Cabal projects with `optimization: 2` globally and
in `package *`. They do not use the workspace development defaults. The
executables and all Cabal-built dependencies use `-O2`. The build audit
checks effective GHC flags and store settings for 53 original
and 100 current dependency units. Compiler-distributed libraries
keep their toolchain settings. They were not rebuilt.
A separate store audit verifies 111 external units for the GHC controls.
The final native and GHC builds each have effective `-O2` compiler-command
evidence for all seven local components in their checked closures.

Both builds and all runs use `nix-shell`, `heavy-management`, and pueue.
The jobs run serially. Each job has a verified 16 GiB cgroup cap and no job
swap. Benchmarks use `+RTS -N1 -M6G -s -RTS`. Small controls use heap caps
of 2 to 4 GiB. These limits stay below the requested 80 GB maximum.

The matrix compares all 27 Table I configurations. The original measurements
come from the all-`-O2` baseline run. Every current configuration has a fresh
run of the selected runtime.
Each process has a 60-second timeout. The paper used 3600 seconds. Every
matrix result below comes from an audited all-`-O2` build. Machine activity differs
between runs. Elapsed-time ratios do not isolate engine speed.

Spectacular runs 100 fresh QuickCheck tests per comparison. Specftacular
uses 1000 shared random cases, eight separately seeded cases, and 32 directed
integer-boundary and list cases. Compiler versions, generators, validation,
pruning, and enumeration differ. The comparison does not isolate the cost of
the automaton implementation.

GNU `time` reports peak RSS in KiB. The tables convert it to MiB. RTS maximum
residency measures the live heap at GC samples. It is not RSS. Allocation is
cumulative traffic, not simultaneous RAM use. A timeout has no final law
count. Its captured output can also omit buffered laws. Counted prefixes include
only newline-terminated equations. A trailing fragment is not another law.

## Results

T means a 60-second timeout. A dash means that the run has no final law
count. HugeLists uses different `usort` definitions: the original preserves
duplicates, while the current benchmark removes them. Its law counts are not
results for identical workloads.

| Signature | Size | Through phase | Original s | Original MiB | Original laws | Specftacular s | Specftacular MiB | Specftacular laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists | 7 | 2 | 1.07 | 21.6 | 32 | 0.37 | 21.3 | 15 |
| Lists | 7 | 3 | 18.11 | 70.8 | 73 | 11.43 | 75.3 | 33 |
| Lists | 7 | 4 | T | 139.5 | — | 26.17 | 193.8 | 41 |
| Octonions | 7 | 2 | 0.15 | 21.4 | 8 | 0.92 | 21.0 | 15 |
| Octonions | 7 | 3 | 0.17 | 20.1 | 8 | 0.91 | 20.8 | 15 |
| Octonions | 7 | 4 | 0.22 | 24.3 | 8 | 0.92 | 21.2 | 15 |
| Regex | 7 | 2 | 3.06 | 18.7 | 42 | 52.04 | 47.2 | 60 |
| Regex | 7 | 3 | 4.29 | 16.8 | 42 | 51.58 | 48.7 | 60 |
| Regex | 7 | 4 | 5.84 | 17.1 | 42 | 52.17 | 48.5 | 60 |
| ListMonad | 7 | 2 | 0.27 | 15.4 | 8 | 3.75 | 39.4 | 9 |
| ListMonad | 7 | 3 | 0.46 | 22.3 | 8 | 3.84 | 39.6 | 9 |
| ListMonad | 7 | 4 | 18.04 | 208.8 | 42 | 7.65 | 187.6 | 9 |
| HugeLists | 3 | 2 | 0.07 | 12.1 | 22 | 0.11 | 17.0 | 28 |
| HugeLists | 3 | 3 | 0.18 | 17.0 | 27 | 0.19 | 22.7 | 40 |
| HugeLists | 3 | 4 | 0.64 | 30.7 | 33 | 1.85 | 50.3 | 46 |
| HugeLists | 4 | 2 | 0.20 | 14.3 | 37 | 0.50 | 26.9 | 46 |
| HugeLists | 4 | 3 | 1.37 | 36.3 | 68 | 1.76 | 69.8 | 84 |
| HugeLists | 4 | 4 | 28.43 | 122.7 | 90 | 12.96 | 159.9 | 125 |
| HugeLists | 5 | 2 | 0.88 | 23.2 | 66 | 6.71 | 174.8 | 92 |
| HugeLists | 5 | 3 | 27.27 | 104.8 | 144 | 37.33 | 516.8 | 197 |
| HugeLists | 5 | 4 | T | 165.1 | — | T | 651.6 | — |
| HugeLists | 6 | 2 | 6.37 | 39.1 | 99 | 10.91 | 250.5 | 130 |
| HugeLists | 6 | 3 | T | 305.6 | — | T | 611.7 | — |
| HugeLists | 6 | 4 | T | 308.9 | — | T | 611.7 | — |
| HugeLists | 7 | 2 | T | 60.2 | — | T | 433.6 | — |
| HugeLists | 7 | 3 | T | 58.0 | — | T | 508.5 | — |
| HugeLists | 7 | 4 | T | 55.6 | — | T | 509.5 | — |

Spectacular completes 20 runs and reaches the limit in 7. Specftacular
completes 21 runs and reaches the limit in 6. No run has an unexpected exit
status.

Lists size 7 through phase 4 completes in Specftacular and reaches the limit
in the original. Regex size 7 through phases 2, 3, and 4 now completes in
both. HugeLists size 5 through phase 3 now also completes in both.
The HugeLists definitions differ as stated above. Both implementations
time out in the other six cells.

Regex remains expensive. Its runs take 51.58 to 52.17 seconds, close to the
60-second limit. Phase 2 allocates 396.615 GiB, versus 17.185 GiB in the
original. The changes remove timeouts without closing this cost difference.

Lists7P4 prints 41 laws in 26.17 seconds. It uses 193.8 MiB peak RSS,
retains 69.6 MiB at the largest GC sample, and allocates 101.061 GiB.
HugeLists5P3 prints 197 laws in 37.33 seconds, uses 516.8 MiB peak RSS,
and allocates 210.460 GiB. The largest observed RSS is 651.6 MiB in the
interrupted HugeLists5P4 run. It is a censored measurement, not a completed
peak for that search.

Selected completed runs have these costs:

| Signature, size, phase | Original allocation GiB | Specftacular allocation GiB | Original residency MiB | Specftacular residency MiB | Original GC CPU s | Specftacular GC CPU s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists-7-p2 | 4.275 | 1.972 | 5.35 | 2.53 | 0.231 | 0.031 |
| Octonions-7-p2 | 0.419 | 2.078 | 12.58 | 2.94 | 0.026 | 0.024 |
| Regex-7-p2 | 17.185 | 396.615 | 4.47 | 11.16 | 0.474 | 1.863 |
| ListMonad-7-p2 | 0.961 | 25.800 | 3.47 | 9.95 | 0.030 | 1.020 |
| ListMonad-7-p4 | 52.501 | 38.832 | 72.02 | 82.68 | 7.004 | 1.790 |
| HugeLists-4-p4 | 126.783 | 70.585 | 39.68 | 63.47 | 8.920 | 2.122 |
| HugeLists-6-p2 | 24.723 | 57.066 | 17.60 | 95.83 | 1.246 | 1.686 |

All 21 configurations that completed at `dd5da750` still complete.
Sixteen retain exactly the same ordered output. Five completed HugeLists
bases omit 14 printed equations in total and add none. HugeLists5P3 omits
seven equations with verified overflow or partiality counterexamples.
The HugeLists4P4 omissions also include a valid zip-empty equation.
A separate typed check derives it from the current HugeLists4P4 rules.
A shorter basis alone does not establish lost coverage or stronger results.
Thirteen completed runs allocate less and eight allocate more than
`dd5da750`. The input domain and some bases changed. These are whole-search
cost comparisons, not identical-work measurements.

The six timeout outputs remain censored. HugeLists5P4 exposes 180 complete
lines. HugeLists6P3 and P4 expose 170 each, versus 76 at `dd5da750`.
The three HugeLists7 runs expose 148 each. These are lower bounds from
buffered output. Trailing numbered fragments do not count as equations.
Neither their lengths nor the unchanged completion count establishes an
overall performance improvement.

An isolated core control explains the corrected HugeLists6 stall. It applies
type-uniform completion with the preceding input policy. The phase-3 size-4
`Int` bucket completes in 2.46 CPU seconds; `dd5da750` spends 49.27 CPU
seconds there before interruption. The control reaches 230 printed laws
and size-6 `Int`, then still reaches the 60-second limit. Its size-5 `Int`
bucket takes 20.58 CPU seconds. These are core-only diagnostics. The matrix
above measures the combined runtime and revised inputs; it has no matching
phase trace. The control does not establish another completed matrix cell.

All twenty configurations that completed at `456123af` also still complete.
Fourteen allocate less and six allocate more. Five increases exceed 5%:

| Completed configuration | Allocation change from `456123af` |
| --- | ---: |
| ListMonad7P2 | +47.42% |
| ListMonad7P3 | +45.16% |
| HugeLists4P2 | +7.26% |
| HugeLists5P2 | +21.88% |
| HugeLists6P2 | +7.89% |

HugeLists4P3 increases by 0.77%. The regressions are not confined to small
workloads. Later phases can benefit: allocation falls by 42.81% for
ListMonad7P4, 37.29% for HugeLists4P4, and 10.16% for Lists7P4. Some
printed bases change relative to `456123af`. These comparisons do not uniformly hold output fixed.

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

### Completed Regex runs expose more general equations

Each completed current Regex size-7 run prints 60 laws. These include general
alternation commutativity and both distribution laws. With shorter variable
names and infix notation, they are:

```text
x | y == y | x
x ; (y | z) == (x ; y) | (x ; z)
(x | y) ; z == (x ; z) | (y ; z)
```

The retained original run prints commutativity instances with `any` and
`e`. It does not print these three general equations. Both runs print
general concatenation associativity. The original also prints seven
associativity instances with `any`. These examples compare the printed
bases. Their counts do not prove semantic coverage or independence.
Regex equality checks acceptance on 100 fixed words. It does not establish
complete language equivalence. The QuickSpec artifact has no saved Regex
output, so it supplies no measured law comparison for this workload.

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
Repeated occurrences must agree. Smaller type sizes come first. Among
equal-sized types, abstract instances precede concrete instances during
exploration. This suppresses many ground consequences.
QuickSpec 2's [polymorphism layer][qs-poly] provides the design reference.

Lists5P4 produces the same 24 numbered laws in native checked execution,
native unchecked execution, and the GHC frontend. There are no exact
text duplicates after law numbers are removed. The normalized law text has
SHA-256 `8088731afcad759c3a22db9f0c34a29b26b8d096115a55d19aa44a4850ec1821`.
Both general laws are present:

```haskell
map f (concat xss) == concat (map (map f) xss)
concat xss ++ concat yss == concat (xss ++ yss)
```

The selected size-5 control also contains
`concat (concat xsss) == concat (map concat xsss)`. It has no exact duplicate
law text. These checks do not establish a minimal or independent law basis.

### Completion follows nested polymorphic consequences

Completion gives distinct names to the term and type variables of each
rule before it computes an overlap. It unifies type constructors and rejects
cyclic term and type substitutions. This permits overlaps that require
`a := [b]` or `a := [[b]]`. A literal annotation comparison misses these
consequences. For example, double reverse, map/reverse, and an earlier
concat/reverse law can prove

```haskell
reverse (concat xss) == concat (reverse (map reverse xss))
```

Current coverage controls load the actual final Rules from three runs.
Their numbered output matches the corresponding production controls exactly.
The checks cover 597 retained target occurrences from earlier Specftacular
outputs. They derive 586. Eleven have independently verified counterexamples;
the bounded prover derives none of those eleven.

| Current control | Printed laws | Retained target corpora | Derived | Independently refuted |
| --- | ---: | --- | ---: | ---: |
| Lists7P4 | 41 | Exact typed 48-, 63-, and 41-law outputs | 152 | 0 |
| HugeLists5P3 | 197 | Earlier 214-law prefix and exact typed 204-law output | 407 | 11 |
| ListMonad6P4 | 9 | Earlier 18-law frontend output and exact typed nine-law output | 27 | 0 |

These are retained Specftacular corpora, not the published Spectacular
artifact. The 214-law HugeLists and 18-law Monad printed targets omit
constant type annotations. Their reconstruction retains rigid given types
and shared variable identity. It freshens constant occurrences and jointly
infers both sides. The stronger reconstructed scheme covers the hidden old
constant instances. Exact typed targets keep their original annotations.
The checker verifies the reconstruction against those typed targets before
it uses this inference policy for the printed-only targets.

The eleven refuted occurrences comprise two total-value counterexamples
and nine partial-context counterexamples. They repeat seven equation forms
across the two HugeLists corpora. They are identified by exact source,
target index, and equation text. Other failed proofs would remain unknown;
they would not become counterexamples. All 586 remaining targets have a
derivation. There are no parse/type failures, proof errors, or timeouts.

The checker first tries direct typed subsumption in both directions, then
normalization. It inserts no old targets and runs no extra completion.
Each target has a two-second proof limit. An independently refuted target
passes its negative check only when the prover returns no derivation.
That bounded result is not a proof of non-derivability or basis consistency.
A separate false concat/reverse equation remains unproved in each control;
`[[1],[2]]` gives a concrete counterexample. These checks establish typed
derivability from tested equations. They do not formally verify Haskell
semantics or prove that a basis is minimal.

The Monad control uses size 6. Its nine-equation output matches all three
frontend controls and differs from the size-7 matrix output. This is not
exhaustive equivalence of all 27 matrix bases.

A separate capture checks the valid equation omitted from HugeLists4P4:

```haskell
zip ([] :: [A]) (ys :: [B]) == zip (xs :: [A]) ([] :: [B])
```

Both sides have result type `[(A,B)]`, with distinct rigid carriers.
Normalization proves the equation from the actual 125-law run's Rules.
The capture reproduces that run's exact output. It inserts no target and
runs no extra completion. Its false concat/reverse control remains unproved.
Other smaller-HugeLists and phase bases were not each checked.

Polymorphic completion has an explicit annotation-depth budget. Program
leaf count alone does not bound type depth. The budget depends on the
requested size and declared signature types. It can omit valid critical
pairs. It is not a completeness bound for the grammar and does not bound
transient unification or normalization cost.

### Higher-order ListMonad coverage improves

The native resolver composes function generators from a `CoArbitrary` domain
and a generated codomain. It supports the `A -> [B]` variables required by
ListMonad. User overrides take priority in random generation. Function values do not receive a
fabricated `Eq` instance. Unsupported generator types produce warnings.
See QuickSpec 2's [generator resolution][qs-generators].

Applications such as `f x` can serve as representatives. The size-4 existing
golden now includes general list-monad left identity:

```haskell
return x >>= f == f x
```

At size 6 through phase 4, native checked execution, native unchecked
execution, and GHC each produce the same nine numbered laws. These include
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
That output keeps `sort` and `usort` distinct. Both selected native and GHC
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

The directed schedule also addresses mixed Int-list values. For `x = 1`
and `xs = [0,maxBound]`, these sides have different total results:

```haskell
sort (map (+ x) xs) == map (+ x) (sort xs)
-- left: [minBound,1]; right: [1,minBound]
```

The duplicate-removing `usort` version fails in the same way. The retained
original HugeLists5P3 output prints the `sort` equation as law 133.
The [published signature][original-hugelist-signature] uses concrete `Int`.

`succ` has a different failure: it throws at `maxBound`. For
`xs = [0,maxBound]`, demanding the first element of
`sort (map succ xs)` throws, while the first element of
`map succ (sort xs)` is 1. The `usort` version has the same difference.
At `xs = [maxBound]`, these three equations also fail:

```haskell
map succ xs == map (+ 1) xs
succ (sum xs) == 1 + sum xs
sum (map succ xs) == sum (length xs : xs)
```

Demanding the left scalar or first list element throws. The corresponding
right result is `minBound`. These equations are unsafe as unconditional
rewrites under non-strict Haskell contexts. Full list equality can throw
rather than return `False`. The controls record that distinction.
The current HugeLists5P3 output omits all seven recorded equation forms.
Its remaining 197 equations retain their previous order.

The schedule preserves the original random cases and eight independent-seed
cases. It retains 32 directed boundary descriptors. At `minBound` and
`maxBound`, a selected concrete Int list contains `[0,boundary]`. The same
innermost pair appears in the existing two nested Int-list types. Other
Int cases retain their earlier policy. Direct values for abstract carriers
and their first three list types also retain their earlier policy.
A list type without a direct boundary value uses its existing generator
at size zero in an inactive slot and size 100 in an active slot. This permits
empty `[Bool]` inputs without changing the scalar boundary or replacing the
generator. A custom generator need not return an empty list at size zero.

Given-variable indexes select slots modulo 4. Some variables therefore
share a presence pattern. Repeated occurrences use the same valuation.
The old take-overflow and asymmetric-list counterexamples remain covered.
`SPECFTACULAR_TESTS` counts only random cases; the default total remains
1040. Direct boundary values can lie outside a custom generator's domain,
as before. Other values come from their declared generators. The shared
lookup uses logical types, so the concrete Int cases do not replace abstract
carrier cases in the GHC frontend. Finite testing still permits false laws
that can affect subsequent pruning.

### Representative instances change the equation basis

With the same nonnegative-integer gcd signature and term size 3, the original
prints 22 laws. The current golden prints six. The paper describes
generalizing discovered laws. The current search also tests instances of
new representatives. These six laws include general commutativity,
idempotence, the zero identity, and three constant reductions.
The original gives commutativity only at the supplied constants 1029, 1071,
and 21. Fewer laws give a more general result in this example.

At Octonions size 7 through phase 2, the current run prints 15 laws. The
original prints 8. The saved QuickSpec output has 15. Equal counts do not
establish equivalent laws. Current equations include flexibility and three
Moufang forms. The original output does not print these forms.

The paper already explains this kind of difference. Section IV-A,
“Differences in Discovered Laws”, describes QuickSpec's schema heuristics and
their effect on Octonion laws. A different basis or orientation is not itself
an error. See QuickSpec 2's [schema layer][qs-schemas].

## Enumeration and pruning

The phase order follows paper section III-C. Each phase visits increasing
program sizes, then type buckets ordered by type size. Among equal-sized
types, abstract carriers precede concrete types.
The search orders ties within a size/type bucket by Knuth-Bendix order.
Smaller terms therefore supply rules before larger terms in that phase.
The search shares rules between phases.

The current partial-term oracle follows section III-D. It suspends a match
when a required subterm is unresolved. It resumes that match when the
subterm expands. A proven match rejects the branch during enumeration,
before the remaining choices expand. Rules are refreshed between size/type
buckets, as section III-E describes. This retains enumeration pruning.
It does not enumerate the complete language before applying templates.

Early templates contain only linear, decreasing rules. A repeated term
variable cannot become independent holes. An annotation can become a hole
only when a principal-type check proves that the rule covers every type
instance of that pattern. Other templates retain exact type annotations.
Typed structural rewriting also checks complete candidates before value
generation. That check can use nonlinear rules. The current search does
not use the published node oracle that the source marks as too strong.

Parametricity also permits reuse across type instances. This requires each
signature constant to be parametric in the abstract carriers. It must not
inspect their representations or capture class dictionaries. A law about
parametric `map` does not need an independent test at every carrier type.
Typed rewriting uses the shared type substitution to apply that law.
This reuses an accepted scheme. Inferring stronger independent type binders
requires the separate validation described below.
Concrete arithmetic types remain rigid. Independently renaming the carriers
of each candidate is insufficient: it can lose comparisons between terms
that the grammar introduces in different phases.

Schema generalization remains in place, as section III-G describes. The
grammar uses one variable of each type. Testing renames variable occurrences
independently and tries more general instances first. A repeated-variable
identity is a search schema, not proof of every renamed equation. Local
checked and unchecked probes find addition commutativity and reject
subtraction commutativity. New representative schemas of up to five leaves
also get instances, following [QuickSpec 2][qs-schemas]. Instance enumeration
uses up to four variable names of each type. The initial most general
instance can use more names.

Cost-centre profiles separated template graph construction, typed
rewriting, input generation, and equality tests. The development runs used
external dependencies at `-O2` and local libraries at `-O0`. Profiling adds
substantial overhead. Completed uninstrumented runs determine which changes
are retained. The selected search uses the suspended oracle. It does not
build an exclusion product for every bucket. These template-index changes
did not modify CFTA.

The selected oracle also skips partial-term reconstruction when no checks
are suspended and the concrete root cannot start a program match. An `app`
root with four children or a `filter` root with two children retains the
original path. A matched O2 control keeps the exact output prefix and
reduces sampled allocation by 1.65% in the completed `Int` bucket. It does
not establish a speed improvement. A pending-representative cache was
rejected: counters found 0.31 pending variable occurrences per callback,
and the matched control did not establish a fixed-work benefit.

A development Lists size-7 profile stopped after 300 seconds. It recorded
284,404,205 calls to `matchPartial` under newly started checks and 2,311,899
under resumed checks. Newly started checks account for 99.2% of those calls.
The current oracle indexes exact template heads
and application counts. It skips only incompatible fixed heads. Wildcards,
prefixes, and unknown heads retain the generic path. The index preserves
template order and duplicates. It does not change suspended matches.

A completed all-`-O2` control before the completion changes varied only
this index. Lists size 7 through
phase 4 allocates 140.93 GiB without it and 121.39 GiB with it, a 13.9%
reduction. Both runs print the same 48 equations in the same order. Peak RSS
is 193.2 and 192.4 MiB. Regex size 4 through phase 2 keeps the same 17 laws;
allocation changes by less than 0.01%. All 88 finite language and order
checks pass. These checks include generic templates, aliases, and duplicate
templates. They support the filter contract; the larger completed run
provides the allocation evidence.

The oracle uses these assumptions. Its holes match independently. A repeated
term variable therefore cannot become independent holes. A template must
prove that every match rewrites to a smaller well-typed term. Type erasure
also needs principal-type coverage and an order that is independent of the
annotations. Equal-weight rules qualify only when function structure or
constant names prove the decrease. These restrictions belong to
Specftacular. They do not change CFTA's template language or formal contracts.

The schema and instance trees check whether existing rules prove equality before they
run the full validation schedule. [QuickSpec 2][qs-terms] makes a similar
check before its tester. New equalities still use every test case.
An ordinary equality exception discards the candidate. Cancellation and timeouts
propagate to the caller.

A separate diagnostic before the completion changes used 100 random cases
plus the same 40 validation cases. It also reached the 60-second limit for
Regex7P2. The `456123af` implementation completes the default-budget matrix cell.

## Completion improvements

Completion rejects incompatible program shapes before typed matching. It
caches normal forms while the rule set stays fixed. Each accepted equation
starts a new cache. Cache keys include all annotations and use structural
equality. The cache holds at most 256 entries. Each key and value has at most
256 term nodes, including annotations. Larger terms normalize without cache
insertion. The size check runs before hashing. It forces each accepted node
and symbol to weak head normal form without forcing symbol payloads. Cache
updates are forced between pairs. Keys and values contain at most 131,072
expanded node occurrences; this does not bound heap bytes. These limits prevent the
large retained terms seen with the rejected unbounded cache.

Completion checks the normalized left-size bound before it normalizes the
right side. Both optimizations require finite, total terms and terminating
normalization. They preserve normal forms under fixed rules. They can change
the demand on partial values. Phase order, increasing size order, and FIFO
critical-pair processing remain in place.

The published artifact's [exact rewrite update][original-rewrites] stores
the larger term's hash with the smaller term. It lists critical-pair
completion as a [TODO][original-completion-todo]. Specftacular performs
ordered completion. This adds work relative to that artifact.

### Rule orientation must survive type substitution

The selected rewriter fixes a defect in the port's rule classification.
The previous classification used an order that could depend on symbolic
type annotations. Renaming or instantiating those types could reverse the
order. Keeping only the first direction then omitted a valid rewrite in
another instance.

A captured HugeLists completion demonstrates the consequence. After 10,000
critical-pair steps, 54 added index entries contain only nine distinct
canonical typed equations. The first repeated equation is not subsumed in its forward direction,
although an existing reverse rule proves it with the actual typed matcher. Canonical renaming then recreates a direction already
in the index. This repeats completion work.

The corrected classification uses `annotationIndependentGreater`. A single
direction requires a decrease that survives shared term and type
substitution. Otherwise, the index retains both directions. Each actual
rewrite still checks the instantiated order. A direction with unbound
right-side variables cannot invent bindings. The proof assumes finite,
well-formed typed terms and separate term and type variable namespaces.
The conservative fallback can create more critical pairs.

Completion must also preserve the type instances of a critical pair. Its
normalization now uses only decreases that hold for every type instance.
An order based on the current symbolic annotations can make a generic pair
look redundant while another instance still needs its equation. Storing
both directions does not repair a pair already discarded by normalization.

The ground-joinability shortcut now requires closed type annotations.
Its term-variable orderings do not cover changes to type-variable order.
A pair with unresolved type variables keeps the ordinary typed checks
and completion path. The existing program-size, annotation-depth, and
term-variable-order budgets remain. These conservative conditions can
retain more equations. They do not prove that completion finishes.

A small typed witness compares `length (fst ([], []))` with
`length (snd ([], []))`, with independent list element types. Both values are
zero. Swapping the element types changes the old order. The corrected rules
handle both orders. Fifteen initial and 44 additional checks cover alpha
renaming, concrete `Int` and `Bool` instances, compound types, stable
one-way rules, and unbound right-side variables. The false concat/reverse
control remains unproved. These checks support the rule-classification
contract. They do not prove completion or confluence for every signature.
This is a correction to Specftacular's rewriter. The paper does not specify
this annotation-sensitive classification, so it is not a new paper erratum.

### Share critical-pair inputs within each batch

The selected rewriter computes the incoming rule's fresh names and left
contexts once per batch. It reuses those terms while visiting the existing
rules. It keeps the original binder names, rule order, overlap order, and
FIFO queue. The change adds no persistent cache.

An all-O2 replay processes the same 10,000 critical pairs before and after
this isolated sharing change. The interval still has pending pairs.
Both runs produce the same 1,066-entry typed
snapshot, with identical index classes, order, and binder names. Sampled
allocation in that interval falls from 10,717,798,480 to 9,679,273,104 bytes,
a reduction of 9.690%. Source inspection preserves the ordered pair stream;
the replay directly checks its final snapshot and step count.

A separate complete HugeLists5P3 control prints the same 204 laws in the
same order. Its whole-process allocation falls by 0.394%. The host is noisy,
and one pair does not establish a timing improvement. The larger replay
reduction applies to its selected completion interval. It does not describe
the whole search. The final matrix also includes the completion and input
corrections described above.

## HugeLists reduction and equation generalization

A later optimized profile of `456123af` assigns 85.4% of application ticks
to structural subsumption and its descendants, excluding GC and PROFILING.
One captured query makes 13,551,744 recursive visits to only 29 distinct
ordered node pairs. Its wider graph is deterministic by symbol and arity.
The original traversal detects cycles on the current path. It repeats work
when different paths reach a shared subgraph.

The [CFTA worklist][cfta-worklist] checks each mandatory pair once per query.
For each narrow edge, it finds unconstrained wider edges with the same
symbol and arity. One such edge makes its child pairs mandatory. Zero
compatible edges reject the query. Multiple compatible edges restart the
original traversal from the query roots.
Empty-node and equal-node shortcuts remain. This requires finite, total,
immutable closed graphs and valid node identities. The visited set can
reach the product of reachable graph sizes. The test remains a sufficient
structural predicate, not a complete language-inclusion procedure.

The explicit-ID replay reproduces the original query result and visit
counts. Both algorithms return `True`. It measures algorithms on a recorded
graph, not native node cost.
A separate O0 grammar control completes 100 reduction passes in 0.682
seconds with the worklist; baseline does not finish within 120 seconds.
The candidate does not reach a fixed point. Baseline has no completed
snapshot, so this is not a completed-work speed ratio. Existing CFTA tests
pass 741 examples. All eight standard cells keep their checksums and pass
the 5% allocation/instruction budget. Their largest increases are 0.00250%
and 0.00167%, respectively. Those checks use the full production manifest
and O2 builds.

The native search then passes the stalled `Int` reduction and reaches 214
printed laws before the limit. An actual size-5 `[A]` bucket profile assigns
96.0% of application ticks to completion. This denominator excludes GC and
PROFILING but retains SYSTEM and IDLE. Allocation and entry counts still
include the prefix. The capture for law 214 permits a fixed-work replay:
checking the normalized left-size bound first avoids right normalization
for 8,268 of 10,000 pairs. Both variants give the same 554-rule snapshot.
Sampled interval allocation falls by 45.27%. Local replay code uses O0;
CFTA and external libraries use O2. The argument requires finite, total
terms and terminating normalization. A changed cache history changes work,
not normal forms under fixed rules. It does not preserve demand behavior
for partial or diverging inputs.

All 178 rules added at that frontier specialize one program equation:

```haskell
length (take (length xs) ys) == length (take (length ys) xs)
-- xs :: [a], ys :: [b]
```

The previous scheme requires the same element type for both lists. With
independent binders, the validated scheme subsumes those 178 additions.
The controlled queue then finishes after 73 steps with no new rules.
This replay keeps the original queue. It does not add overlaps for the
injected diagnostic rule, so it does not establish closure of that theory.
[QuickSpec 2's regeneralise method][qs-regeneralise] supplies the inference
approach. It retains concrete constructors and restores the constraints
from applications, repeated variables, and both result types. Its unit-type
counterexample explains why a whole variable type cannot become a fresh
type variable.

Specftacular's [`generalizeLaw`](../src/Specftacular/Rewriting.hs) retains
original variable identity across both sides. It freshens each constant
occurrence's declared scheme but keeps its shared binders. Given instances
keep their declared types. One shared match must recover both original
sides before canonical renaming. Typing alone does not accept a proposal.
Independent binders get distinct carriers from `A` through `Acc`, and each
term variable gets a fresh generator at its inferred type. Both sides must
compile at the original result type. Validation uses the decision tree's
actual equality function and the full shared schedule, 1040 cases by
default. False, untestable, unsupported, or changed-result proposals retain
the original law. Cancellation and type errors propagate. Generated values
are not retagged.

The original HugeLists5P3 result has 144 laws and different `usort`
semantics. Its output and workload differ from the current matrix.
The measurements do not establish an equal-work speedup.

Against `456123af`, the Lists4P1 control at `9be187a0` allocates 15.826%
more and uses 17.002% more Cachegrind instructions. Both print the same ten program equations, but three selected
schemes have independent carrier types. Setting `B = A` recovers the old
schemes. This is not byte-identical output.
These controls exceed the repository's 5% budget. We accept the measured
Specftacular costs to learn independent type schemes earlier and retain
the full validation schedule. The
profile-guided prototype and production matrix support that tradeoff:
HugeLists5P3 now completes, all twenty earlier completions remain, and
several later phases allocate less. This is not a universal speedup or a
passed 5% gate. The separate eight standard CFTA cells pass their budget.

A fresh Lists4P1 control compares `102965d3` with `dd5da750`. Both print
the same ten typed equations in the same order. Allocation rises by 0.01647%
and Cachegrind instructions rise by 0.00408%. The input domain changed.
This incremental control passes the 5% budget. It does not remove the
earlier accepted cost increase relative to `456123af`.

## Profiling that guided the selected changes

The first two profiles measure `9be187a0`, before the orientation and
sharing changes. The third measures `dd5da750`, before type-uniform
completion. They identify the work that led to the selected changes.
They do not measure `102965d3`'s cost distribution. All local modules,
CFTA, and external Cabal dependencies use O2.

Native diagnostics record actual phase and size/type bucket boundaries.
The through-phase setting only stops execution at a phase boundary. A later
requested phase therefore shares the earlier ordered search prefix for the
same size. This does not make separate timing samples interchangeable.
Only complete, newline-terminated equations count as captured output.
A timeout can leave buffered equations and a trailing fragment.

The [cost-centre timer][ghc-profile-timer] starts at the selected bucket. Each window lasts up
to 180 seconds. The denominator below excludes GC and PROFILING self ticks.
It retains SYSTEM and IDLE. Each self tick is assigned once. Attribution
uses [source paths][ghc-costs] and explicit value-operation corrections for lazy
construction ancestry. It remains a source-based interpretation.

| Source | Requested size | Actual phase and bucket | Application/runtime ticks | Main cost |
| --- | --- | --- | ---: | --- |
| `9be187a0` | HugeLists 5 | Phase 3, size 5 `Int` | 136,365 | Enumeration and pruning: 99.43% |
| `9be187a0` | HugeLists 7 | Phase 1, size 6 `[A]` | 163,347 | Completion: 94.27% |
| [`dd5da750`](https://github.com/TharkunAB/cfta/tree/dd5da750997102601e4156ffe38668bd7ebf2cc1/specftacular) | HugeLists 6 | Phase 3, size 4 `Int` | 135,717 | Completion: 98.25% |

The size-5 profile remains in enumeration before its first candidate. It
samples no completion or input generation in that window. The corresponding
native bucket completes in about 20 CPU seconds. Profiling changes the cost:
PROFILING consumes 23.22% of all ticks in this window.

The size-7 profile retains the native 113-law prefix. Left and right
normalization use 66.09% of application/runtime ticks. Critical-pair
generation uses 24.49%. Shape matching uses 33.31% inside the normalization
paths. Renaming uses 10.81% inside critical-pair generation. The nested
figures must not be added to their parent costs. These findings led to the
captured completion, the orientation correction, and shared batch inputs.

The size-6 profile reaches its 180-second limit in completion.
Normalization uses 64.55% of application/runtime ticks, critical-pair
generation 28.63%, and ground joinability 3.96%. Enumeration and pruning
use 0.65%. A captured 10,000-step completion adds 226 distinct typed
entries. Of these, 222 share this erased equation family:

```haskell
length (take (length xs) (sort ys)) == length (take (length xs) ys)
-- xs :: [a], ys :: [Int]
```

Joint renaming of term and type binders reveals no increase in duplicate
entries. Exact duplicate suppression does not address this measured growth.
A focused probe uses actual critical pairs from the captured rules. The
old normalizer discards a generic pair as equal, but a closed type instance
still needs the equation under the same Rules. Uniform normalization retains
the pair. The old ground-joinability shortcut would then discard it again.
Both corrections are necessary for this witness. All 16 typed probe reports
complete, and both false concat/reverse controls remain unproved.

Only ticks belong to the selected timer windows. Profile allocation and
entry counts include the preceding search. No profile finishes its selected
bucket. Their elapsed times cannot supply a completed-work speed ratio.
Their differing costs also rule out one explanation for every HugeLists
timeout.

## Memory and allocation

QuickSpec 2's sparse [decision tree][qs-tree] retains counterexamples that
separate representatives. The current engine follows that design. A leaf
retains a term evaluator. A branch retains one discriminator case and its
values. Test cases store seeds and boundary indexes. Each comparison generates
only the variables used by either term. Both evaluators use the same valuation
for that case. The tree retains a valuation only through discriminator values.
It does not retain all generated
nested lists and complete result vectors at every representative.

A local control before the completion changes restores shared input maps
and retained result vectors. It also restores the legacy decision tree's prefix
comparisons. It keeps the same pruning, proof shortcut, and available
validation cases. The strategies compare cases in different orders.
They can therefore treat partial values differently. This control compares
evaluation strategies, including storage. It does not isolate storage alone.
All variants produce the same 29 numbered Lists5P4 laws.

| Lists5P4 storage control before completion changes, 1000 + 40 cases | Peak RSS, MiB | Allocated, GiB |
| --- | ---: | ---: |
| Shared inputs and retained result vectors | 1920.5 | 20.93 |
| Sparse evaluation | 51.4 | 20.59 |
| Sparse evaluation with native runtime checks | 54.2 | 21.36 |

Fresh `102965d3` controls have these peak RSS values. The GHC process
includes the compiler and interpreter.

| Control | Native unchecked MiB | Native checked MiB | GHC MiB |
| --- | ---: | ---: | ---: |
| Lists5P4 | 49.2 | 54.5 | 528.9 |
| ListMonad6P4 | 86.7 | 93.0 | 546.7 |

All three modes produce the same ordered 24-law Lists5P4 output and
nine-law ListMonad6P4 output. These are smaller bases than the historical
storage-control outputs. Agreement does not prove coverage equivalence.

Sparse evaluation regenerates inputs to reduce retained memory.
In the storage control, it uses 97.3% less peak RSS and allocates 1.6% less. Retaining the
complete input maps and result vectors restores the large peak. These
controls do not establish an isolated automaton speed improvement.

On Lists4P1, Cachegrind records 1,426,503,315 instructions for retained
vectors and 445,870,706 for sparse evaluation. RTS allocation is 521,257,520
and 178,430,168 bytes respectively. These controls vary the evaluation
strategy in the same source revision. They precede the completion changes
measured above.

## GHC frontend

`specftacular-ghc` shares the type checks, rewrite rules, validation schedule,
partial-term oracle, and sparse evaluator. It assigns distinct carriers to unconstrained type
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

The session compiles carrier payloads at `Int`. Its resolver can reuse a
generator or equality for a new logical type only when both types have the
same physical type tree. It updates logical names and prefixes. Fresh
`[B]` and `C -> D` generator probes pass. This fallback does not add runtime
type checks.

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
   [oracle][original-node-oracle] can discard a node when only some terms match. The source marks
   that case as too strong. Current structural matching records shared term
   and type substitutions. Repeated variables must match equal subterms.
   Current partial-term pruning uses linear typed patterns and suspends
   unresolved matches. It does not use that node oracle. See the
   [published matcher][original-matcher] and [current rewriter](../src/Specftacular/Rewriting.hs).

3. **Representative instances improve coverage.** Section III-G generalizes
   discovered laws. The current search also tests independent variable
   assignments of new representative schemas through five leaves. This
   recovers general gcd commutativity that the original misses. The fix
   changes the equation basis. Section IV-A already explains schema-related
   basis differences. Raw law counts are not counts of independent facts.

4. **Type checking must include each polymorphic occurrence.** The original
   uses unqualified names and unchecked coercions. The port also had a
   restriction that rejected valid nested list instances. The current code
   qualifies type constructors, checks occurrences and applications, and
   preserves specialized native `Dynamic` types. Generated variables keep
   their declared types during compilation and matching. Validated
   generalization creates new variables at the inferred types. It does not
   change the type of an old generated value. GHC session values retain
   erased runtime types. See the
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
   Directed cases address the recorded overflow and list counterexamples.
   The original artifact rerun also prints `sort`/map-addition law 133 and
   `sort`/map-`succ` law 97 in HugeLists5P3. The former has unequal total
   results; the latter differs under partial-result observations. That run
   also prints map-`succ`/map-addition law 138. These are artifact findings;
   the paper does not print those individual equations. Neither the directed
   cases nor the larger random budget prove the surviving laws.

9. **The artifact does not register the suspended matches from section III-D.**
   The [published matcher][original-matcher] comments out both calls that
   register checks on unresolved holes. Its dependency map starts empty.
   Its registration helpers use `IntMap.adjust`, which does not insert a
   missing key. The current oracle records branch-local pending matches
   and resumes them through the current union-find representatives. This
   implements the paper's described strategy.

## Limits and remaining work

Phases 2 to 4 remain experimental. `ftacularSpec` runs phase 1. This report
calls `experimentalPhases` for later phases. The type-depth budget can omit
completion consequences. The output is not proved minimal or complete.

Validated generalization supports at most five independent type binders
and keeps the original result type and equality function. Missing
generators or failed validation retain the original equation. The checks
depend on parametric signature constants. They neither prove a free theorem
nor test every type. A finite test can still admit a false scheme that
affects subsequent pruning. The reduction replay also reaches its existing
100-pass limit without a fixed point; the worklist does not remove that
budget.

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
checks apply. Fourteen focused inference controls and native checked/untyped
proposal probes check independent carriers, missing instances, false laws,
the actual equality policy, and cancellation. Raw measurements, CSVs,
source checkouts, and local task notes
remain outside this package. This report contains the results and the
source references needed to interpret them.

[original-matcher]: https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/src/Data/ECTA/Internal/ECTA/Enumeration.hs#L411
[original-node-oracle]: https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/spectacular/src/Spectacular.hs#L330
[qs-arith]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal.hs#L423
[qs-driver]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L737
[qs-paper]: https://doi.org/10.1017/S0956796817000090
[qs-schemas]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Schemas.hs#L70
[qs-poly]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Polymorphic.hs#L44
[qs-regeneralise]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Polymorphic.hs#L139-L183
[qs-generators]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L326
[qs-tree]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Testing/DecisionTree.hs#L42
[qs-lists-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/Lists.output
[qs-monad-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/ListMonad.output
[qs-octonions-output]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/examples/tests/Octonions.output

[qs-observe]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Haskell.hs#L181

[qs-terms]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Terms.hs#L70

[original-rewrites]: https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/spectacular/src/Spectacular.hs#L269
[original-completion-todo]: https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/spectacular/src/Spectacular.hs#L771
[ghc-costs]: https://downloads.haskell.org/ghc/9.14.1/docs/users_guide/profiling.html#rules-for-attributing-costs
[ghc-profile-timer]: https://downloads.haskell.org/ghc/9.14.1/docs/users_guide/profiling.html#rts-flag---no-automatic-time-samples
[diagnostic-source]: https://github.com/TharkunAB/cfta/tree/9be187a0168db37d041b0478d605d6758f3598a9/specftacular
[cfta-worklist]: https://github.com/TharkunAB/cfta/blob/d8e95efd0d5005a068bb6872cbcafb1dcd1030a4/cfta/src/Data/CFTA/Interned/Operations.hs#L658
[original-hugelist-signature]: https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/spectacular/benchmarks/HugeLists.hs#L18

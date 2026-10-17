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
equation schemes before it adds their rules. The fresh matrix completes
21 of 27 configurations, including HugeLists size 5 through phase 3.
Six HugeLists configurations still reach the limit.
The machine has other activity. Elapsed time alone does not isolate engine
speed. The controls below record both savings and regressions.

## Sources and method

The runs took place on 2026-10-17.

| Input | Revision |
| --- | --- |
| [Published Spectacular artifact](https://zenodo.org/records/7565003) | `00621f4f0f03e5d0afea3c730434a8842e473546` |
| [Current Specftacular](https://github.com/TharkunAB/cfta/tree/8cef38c5d5a18036fbb4ad19afe864610040e56d/specftacular) | `8cef38c5` |
| [Earlier diagnostic instrumentation][diagnostic-source] | `c47a1d8b` |
| [Published QuickSpec 2 benchmark artifact](https://zenodo.org/records/7565011) | Version 2.1.5, commit `967151eae493fa08a414386cdfb5ce7072477972` |
| [Extended ICST paper](https://mpg.is/papers/gissurarson2023spectacular-extended.pdf) | PDF SHA-256 `44fcc9a6c67a5ddefccb29c37ce721a354b427bc99d6a01dadbb5b9355535882` |

All 63 Haskell files in the Spectacular archive remain unchanged. Its ZIP
SHA-256 is `48ff8dc6671edd9636c3d2c44928aab80fd3c0f92cb56d380ece8a3ae0ca3fa0`.
The QuickSpec ZIP SHA-256 is
`3de3b0cb9c1411f81a329ea3a39b2be92c346bbdc4b5f61718f966ff930c3a91`.
QuickSpec 2 was not rerun. Its source and saved outputs provide reference
evidence.

The selected native runtime is `f54d56c5`. Revision `8cef38c5` also resolves
generalized logical carrier types in the GHC frontend. The current columns
below come from a fresh complete matrix of that runtime.
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
count. Its captured output can also omit buffered laws.

## Results

T means a 60-second timeout. A dash means that the run has no final law
count. HugeLists uses different `usort` definitions: the original preserves
duplicates, while the current benchmark removes them. Its law counts are not
results for identical workloads.

| Signature | Size | Through phase | Original s | Original MiB | Original laws | Specftacular s | Specftacular MiB | Specftacular laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists | 7 | 2 | 1.07 | 21.6 | 32 | 0.37 | 21.5 | 15 |
| Lists | 7 | 3 | 18.11 | 70.8 | 73 | 11.68 | 88.7 | 33 |
| Lists | 7 | 4 | T | 139.5 | — | 26.95 | 198.4 | 41 |
| Octonions | 7 | 2 | 0.15 | 21.4 | 8 | 0.96 | 20.9 | 15 |
| Octonions | 7 | 3 | 0.17 | 20.1 | 8 | 0.96 | 20.9 | 15 |
| Octonions | 7 | 4 | 0.22 | 24.3 | 8 | 0.93 | 20.9 | 15 |
| Regex | 7 | 2 | 3.06 | 18.7 | 42 | 54.49 | 46.6 | 60 |
| Regex | 7 | 3 | 4.29 | 16.8 | 42 | 54.88 | 47.4 | 60 |
| Regex | 7 | 4 | 5.84 | 17.1 | 42 | 55.07 | 47.4 | 60 |
| ListMonad | 7 | 2 | 0.27 | 15.4 | 8 | 3.73 | 38.7 | 9 |
| ListMonad | 7 | 3 | 0.46 | 22.3 | 8 | 4.09 | 38.5 | 9 |
| ListMonad | 7 | 4 | 18.04 | 208.8 | 42 | 7.90 | 186.5 | 9 |
| HugeLists | 3 | 2 | 0.07 | 12.1 | 22 | 0.12 | 17.7 | 28 |
| HugeLists | 3 | 3 | 0.18 | 17.0 | 27 | 0.19 | 22.6 | 40 |
| HugeLists | 3 | 4 | 0.64 | 30.7 | 33 | 1.85 | 50.2 | 46 |
| HugeLists | 4 | 2 | 0.20 | 14.3 | 37 | 0.52 | 26.7 | 46 |
| HugeLists | 4 | 3 | 1.37 | 36.3 | 68 | 1.86 | 70.8 | 86 |
| HugeLists | 4 | 4 | 28.43 | 122.7 | 90 | 12.49 | 157.6 | 128 |
| HugeLists | 5 | 2 | 0.88 | 23.2 | 66 | 6.78 | 171.9 | 93 |
| HugeLists | 5 | 3 | 27.27 | 104.8 | 144 | 35.66 | 516.5 | 204 |
| HugeLists | 5 | 4 | T | 165.1 | — | T | 629.8 | — |
| HugeLists | 6 | 2 | 6.37 | 39.1 | 99 | 10.81 | 217.6 | 131 |
| HugeLists | 6 | 3 | T | 305.6 | — | T | 592.8 | — |
| HugeLists | 6 | 4 | T | 308.9 | — | T | 592.6 | — |
| HugeLists | 7 | 2 | T | 60.2 | — | T | 245.5 | — |
| HugeLists | 7 | 3 | T | 58.0 | — | T | 245.5 | — |
| HugeLists | 7 | 4 | T | 55.6 | — | T | 245.6 | — |

Spectacular completes 20 runs and reaches the limit in 7. Specftacular
completes 21 runs and reaches the limit in 6. No run has an unexpected exit
status.

Lists size 7 through phase 4 completes in Specftacular and reaches the limit
in the original. Regex size 7 through phases 2, 3, and 4 now completes in
both. HugeLists size 5 through phase 3 now also completes in both.
The HugeLists definitions differ as stated above. Both implementations
time out in the other six cells.

Regex remains expensive. Its runs take 54.49 to 55.07 seconds, close to the
60-second limit. Phase 2 allocates 398.760 GiB, versus 17.185 GiB in the
original. The changes remove timeouts without closing this cost difference.

Lists7P4 prints 41 laws in 26.95 seconds. It uses 198.4 MiB peak RSS,
retains 63.8 MiB at the largest GC sample, and allocates 101.785 GiB.
HugeLists5P3 prints 204 laws in 35.66 seconds, uses 516.5 MiB peak RSS,
and allocates 209.846 GiB. The largest observed RSS is 629.8 MiB in the
interrupted HugeLists5P4 run. It is a censored measurement, not a completed
peak for that search.

Selected completed runs have these costs:

| Signature, size, phase | Original allocation GiB | Specftacular allocation GiB | Original residency MiB | Specftacular residency MiB | Original GC CPU s | Specftacular GC CPU s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists-7-p2 | 4.275 | 2.029 | 5.35 | 2.59 | 0.231 | 0.030 |
| Octonions-7-p2 | 0.419 | 2.098 | 12.58 | 3.06 | 0.026 | 0.025 |
| Regex-7-p2 | 17.185 | 398.760 | 4.47 | 11.11 | 0.474 | 1.982 |
| ListMonad-7-p2 | 0.961 | 25.913 | 3.47 | 11.07 | 0.030 | 1.011 |
| ListMonad-7-p4 | 52.501 | 38.945 | 72.02 | 82.68 | 7.004 | 1.925 |
| HugeLists-4-p4 | 126.783 | 70.277 | 39.68 | 57.55 | 8.920 | 2.019 |
| HugeLists-6-p2 | 24.723 | 58.400 | 17.60 | 76.17 | 1.246 | 1.615 |

All twenty configurations that completed at `456123af` still complete.
Fourteen allocate less and six allocate more. Five increases exceed 5%:

| Completed configuration | Allocation change from `456123af` |
| --- | ---: |
| ListMonad7P2 | +48.07% |
| ListMonad7P3 | +45.78% |
| HugeLists4P2 | +8.00% |
| HugeLists4P3 | +0.41% |
| HugeLists5P2 | +21.98% |
| HugeLists6P2 | +10.41% |

The regressions are not confined to small workloads. Later phases can
benefit: allocation falls by 42.64% for ListMonad7P4, 37.56% for
HugeLists4P4, and 9.52% for Lists7P4. Some printed bases change. These
complete-configuration comparisons do not uniformly hold output fixed.

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

Coverage controls load the actual final Rules from three selected runs.
Their numbered output matches the corresponding production controls
exactly. All 343 retained target equations follow:

| Current control | Printed laws | Retained target corpus | Derived |
| --- | ---: | --- | ---: |
| Lists7P4 | 41 | Exact typed 48-law selected output and earlier 63-law Specftacular output | 111/111 |
| HugeLists5P3 | 204 | Earlier 214-law worklist prefix | 214/214 |
| ListMonad6P4 | 9 | Earlier 18-law frontend output | 18/18 |

The 63-law Lists corpus is earlier Specftacular output, not the published
Spectacular artifact. HugeLists and Monad printed targets omit constant
type annotations. Their reconstruction retains rigid given types and
shared variable identity, freshens constant occurrences, and jointly
infers both sides. It gives a stronger scheme whose instances include the
hidden old constant instances. This reconstruction is first checked
against the exact typed Lists targets.

The checker inserts no old targets and runs no extra completion. Each
target has a two-second proof limit. No target has a parse/type failure or
remains unproved. A false concat/reverse equation remains unproved; a
concrete counterexample also confirms that it is false. These checks establish
derivability from tested equations under the stated annotation policy. They do not formally
verify Haskell semantics or prove that a basis is minimal.

The Monad control uses size 6. Its nine-equation output differs from the
size-7 matrix output. Other phase and smaller-HugeLists bases were not each
checked. This is not exhaustive equivalence of all 27 matrix bases.

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

The current schedule preserves the original random cases. It adds eight
independent-seed cases and 32 cases that combine integer boundaries with
empty and singleton lists. Both counterexamples occur with 100 and with
1000 random cases. A native checked reduced HugeLists signature still
finds `xs == take n xs ++ drop n xs`. `SPECFTACULAR_TESTS` counts only the
random cases. The total is that count plus 40. The 32 directed cases supply
values for `Int`, the abstract carriers, and their first three list types.
They can therefore supply values outside a custom generator for those types.
Other types use their generators. These cases fix the recorded failures. Finite testing can still admit false laws that affect later pruning.

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

The profiles identified repeated normalization and typed matching as the
main completion costs. The implementation uses these checks and bounded reuse:

- Check program symbols and application structure before typed matching.
  A template variable still accepts any annotated subtree. A successful
  shape check proceeds through every original annotation and binding check.
- Cache whole-term normal forms while the completion rule set is fixed.
  Start a new cache whenever completion adds an equation. The key includes
  every type annotation. Structural equality checks hash collisions.

Both changes operate on finite, total internal terms. They can demand a
partial Haskell value earlier. The cache holds at most 256 entries. Both
the input and its normal form must have at most 256 term nodes, including
annotations. Input size is checked before hashing. Oversized results are
not inserted. Terms outside these limits still normalize normally.
The cache clears before an insertion into a full table.
The eligibility check evaluates each accepted term node and symbol to weak
head normal form. It does not force symbol payloads. Cache updates are
forced between critical pairs. This prevents deferred updates from retaining
old tables or large unevaluated results. Keys and values contain at most
131,072 expanded term-node occurrences. This is not a bound on total heap
bytes. These earlier matcher and cache changes did not modify CFTA.
The search retains phase order, increasing size order, and FIFO critical-pair
processing. The selected runtime also checks the normalized left-size bound
before it normalizes the right side. It validates proposed equation schemes
before it adds their rules.

A local replay isolates completion from enumeration and value generation.
It captures the actual typed inputs of Regex7P1. It completes the first 22
laws and processes exactly 10,000 critical pairs for law 23. This limit
exists only in the replay. Production completion keeps its existing policy.
Serialization preserves term structure, but not the original heap sharing.
Both variants produce the same 193-rule snapshot, including index
classes, rule order, annotations, and binder names.

Every component uses `-O2`. CPU time covers the final bounded completion
interval. Allocation and peak RSS cover the whole replay, including the
prefix and snapshot output. CPU times remain observations on a noisy host.

| Replay variant | Completion CPU s | Whole allocation GiB | Peak RSS MiB |
| --- | ---: | ---: | ---: |
| Before both changes | 6.721 | 57.463 | 15.1 |
| `456123af`, shape check and bounded cache | 3.139 | 26.393 | 15.6 |

The combined change reduces whole-replay allocation by 54.1%. Sampled
allocation within the completion interval falls by 54.2%. Observed CPU
time falls by 53.3%. A separate complete Lists4P1 Cachegrind control uses
2.92% fewer instructions and 2.88% less allocation. Its ten laws are
identical. Checked and unchecked golden tests pass. A finite matcher check
compares 7,386,314 pattern, target, and initial-substitution combinations.
It checks complete returned substitutions, including conflicts and malformed
annotations. It finds no difference from the original matcher.

The all-`-O2` matrix at `456123af` uses that production implementation.
All three Regex configurations finish within the 60-second limit. The fixed-work replay
compares both changes at the same completion frontier. It excludes the
extra work that these completed searches can now reach.

At `456123af`, all 17 configurations that completed before those changes
still complete.
Their full numbered law sequences remain identical. Each allocates less:
the reductions range from 0.5% to 36.1%. Lists7P4 allocates 7.3% less and
HugeLists6P2 allocates 22.6% less. These completed searches provide evidence
beyond the bounded replay and small instruction control.

An unbounded cache was rejected after a HugeLists6P3 control reached
5092.3 MiB RSS. Resetting the cache after 128 critical pairs still reached
3458.5 MiB. Limiting entry count did not limit the retained term sizes.
The `456123af` size-bounded cache reaches 525.3 MiB in the same 60-second
control. These timeout runs can reach different amounts of work. They are
memory checks, not fixed-work allocation or speed comparisons.

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

The final O2 matrix completes HugeLists5P3 with 204 laws in 35.66 wall
seconds and 35.674 RTS CPU seconds, at 516.5 MiB peak RSS.
The original's 27.27-second result has 144 laws and different `usort`
semantics. These are not identical outputs or workloads. They do not
establish an equal-work speedup.

Against `456123af`, the selected Lists4P1 control allocates 15.826% more
and uses 17.002% more Cachegrind
instructions. Both print the same ten program equations, but three selected
schemes have independent carrier types. Setting `B = A` recovers the old
schemes. This is not byte-identical output.
These controls exceed the repository's 5% budget. We accept the measured
Specftacular costs to learn independent type schemes earlier and retain
the full validation schedule. The
profile-guided prototype and production matrix support that tradeoff:
HugeLists5P3 now completes, all twenty earlier completions remain, and
several later phases allocate less. This is not a universal speedup or a
passed 5% gate. The separate eight standard CFTA cells pass their budget.

## Profiling that guided the completion changes

These all-`-O2` traces describe the ten timeout configurations before
`456123af`. They identified the optimization targets. Their costs and phase
frontiers are historical diagnostics, not current matrix measurements.
The [diagnostic build][diagnostic-source] adds optional instrumentation.
The local
drivers use an internal 60-second timeout. Cancellation closes the active
intervals and permits a normal exit with RTS statistics. The process has the
same 16 GiB cap, zero swap, one capability, and a 6 GiB RTS heap limit.

The traces use `SPECFTACULAR_DIAGNOSTICS=phases`. This mode records phase
and size/type bucket boundaries. Process CPU includes GC. Allocation and GC
differences use sampled RTS counters. No collection is forced. A dash means
that the run does not reach the phase. T marks the interrupted phase.

| Configuration | Phase 1 CPU s | Phase 2 CPU s | Phase 3 CPU s | Phase 4 CPU s |
| --- | ---: | ---: | ---: | ---: |
| HugeLists-5-p3 | 5.50 | 1.03 | 53.60 T | — |
| HugeLists-5-p4 | 5.41 | 0.99 | 53.71 T | — |
| HugeLists-6-p3 | 9.66 | 2.59 | 47.84 T | — |
| HugeLists-6-p4 | 9.69 | 2.56 | 47.89 T | — |
| HugeLists-7-p2 | 60.09 T | — | — | — |
| HugeLists-7-p3 | 60.14 T | — | — | — |
| HugeLists-7-p4 | 60.13 T | — | — | — |
| Regex-7-p2 | 60.12 T | — | — | — |
| Regex-7-p3 | 60.09 T | — | — | — |
| Regex-7-p4 | 60.13 T | — | — | — |

In this historical trace, six configurations stop in phase 1 and four in
phase 3. None reaches phase 4. A through-phase label does not identify the
phase that consumes the time budget.

The through-phase-4 runs provide these per-phase counter samples:

| Signature and size | Actual phase | Allocated GiB | GC CPU s |
| --- | ---: | ---: | ---: |
| HugeLists-5 | 1 | 28.42 | 1.18 |
| HugeLists-5 | 2 | 4.72 | 0.06 |
| HugeLists-5 | 3 | 220.88 | 0.64 |
| HugeLists-6 | 1 | 54.21 | 1.37 |
| HugeLists-6 | 2 | 14.18 | 0.22 |
| HugeLists-6 | 3 | 90.20 | 6.57 |
| HugeLists-7 | 1 | 384.74 | 3.68 |
| Regex-7 | 1 | 487.18 | 1.87 |

Regex spends 56.54 CPU seconds in its phase-1 size-5 Regex bucket.
HugeLists5 spends 51.64 CPU seconds in its phase-3 size-5 `Int` bucket.
HugeLists6 spends 47.16 CPU seconds in its phase-3 size-4 `Int` bucket.
HugeLists7 spreads phase-1 work across buckets. Its size-6 `[A]` bucket takes
19.05 CPU seconds and its size-7 `Int` bucket takes 17.90. The final active
size-7 `[A]` bucket takes only 0.34 seconds before interruption. The final
active bucket is therefore not always the largest cost.

Peak RSS is 19.3, 210.6, 448.7, and 379.3 MiB for those four runs,
respectively. Allocation traffic is large, but these runs do not approach
the memory cap. GC is not the main cost of the stalled phases.

A completed Lists7P4 control checks the instrumentation. All four variants
print the same 48 numbered laws in the same order.

| Lists7P4 diagnostic variant before completion changes | CPU s | Allocated GiB | Peak RSS MiB |
| --- | ---: | ---: | ---: |
| Before diagnostic hooks | 28.06 | 121.3917 | 192.1 |
| Diagnostics off | 28.64 | 121.3938 | 198.0 |
| Phase and bucket tracing | 28.29 | 121.4557 | 190.5 |
| Detailed tracing | 36.74 | 124.7925 | 195.1 |

Diagnostics off adds 0.0017% allocation. Phase tracing adds 0.0510% over
that. Detailed tracing adds 2.80% allocation and 28.3% observed CPU time on
this control. These are single runs. The CPU differences are observations,
not precise overhead estimates on a shared host.

A smaller Lists4P1 Cachegrind control checks default-off instructions.
The count changes from 445,872,006 to 446,092,506, an increase of 0.0495%.
Allocation changes from 178,429,528 to 178,561,608 bytes, an increase of
0.0740%. Both runs print the same ten laws. The existing golden suite also
passes in checked and unchecked modes with phase tracing enabled.

Detailed tracing is unsuitable for identifying production timeout phases.
In HugeLists5 it emits about 195,000 events and remains in phase 1 at the
limit. The phase-only run finishes that phase in 5.4 CPU seconds. Detailed
mode also moves rule completion to an explicit WHNF boundary. Its stage
intervals include demanded lazy work and logging. Decision-tree insertion
includes proofs, compilation, generation, evaluation, and equality. It is
not a measurement of QuickCheck generation alone.

The published artifact's [exact rewrite update][original-rewrites] stores
the larger term's hash with the smaller term. It lists critical-pair
completion as a [TODO][original-completion-todo]. The current engine performs ordered
completion. Its cost is additional work relative to that artifact. It must
be separated from enumeration and template application when interpreting
performance differences.

Two audited cost-centre builds use local O0 and local O2 respectively.
Both use the same five external O2 profiling dependencies. Toolchain
libraries retain their supplied settings. The copies omit the unused
LiquidFixpoint integration from the CFTA manifest. Those earlier copies
did not change CFTA library source. Specftacular adds SCCs and a phase-timer
wrapper without changing the search, seeds, schedule, or forcing points.

Sampling starts only in the selected actual phase, after the unchanged
prefix. Windows have 180-second limits; extended HugeLists7 uses 420
seconds. A 600-second whole-driver guard permits normal cancellation and
profile output. [Thunk cost-centre ancestry][ghc-costs] can name an earlier
phase. [Timer control][ghc-profile-timer] identifies the actual window.
Allocation and entry counts still include the prefix. SCCs can change
optimization and execution costs. Neither build measures production speed.

The analysis counts self ticks once and checks function/dictionary contexts
against source. Regex NFA execution remains equality work even under a
restored signature-construction stack. Groups are source interpretations,
not exact dynamic stage boundaries. GC and PROFILING remain separate.

The following table uses the optimized profiles. Each percentage divides
exclusive self ticks by the ticks left after removing GC and PROFILING.
Other includes schema and instance assignment, tree navigation, SYSTEM,
and unclassified work. Complete means that the selected phase finishes
in the profiling run. It does not replace a native matrix result.

| Signature and size | Actual phase | Window result | Completion | Grammar and pruning | Types and proofs | Input generation | Evaluation and equality | Other |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Regex-7 | 1 | 180 s limit | 84.1% | 0.1% | 0.2% | 0.1% | 14.6% | 0.9% |
| HugeLists-5 | 1 | Complete | 1.3% | 3.3% | 18.9% | 58.3% | 6.7% | 11.5% |
| HugeLists-5 | 2 | Complete | 6.5% | 13.2% | 25.7% | 32.8% | 3.3% | 18.5% |
| HugeLists-5 | 3 | 180 s limit | 0.7% | 95.2% | 1.5% | 1.3% | 0.4% | 0.8% |
| HugeLists-6 | 1 | Complete | 10.0% | 16.2% | 24.7% | 35.9% | 4.6% | 8.6% |
| HugeLists-6 | 2 | Complete | 25.8% | 24.7% | 21.4% | 16.4% | 1.9% | 9.8% |
| HugeLists-6 | 3 | 180 s limit | 97.9% | 0.9% | 0.3% | 0.1% | 0.0% | 0.7% |
| HugeLists-7 | 1 | 420 s limit | 40.4% | 23.0% | 25.0% | 7.1% | 1.1% | 3.4% |

The initial HugeLists7 window reaches size-7 `A` but does not reach
size-7 `Int`. The extended window includes both large native buckets.
It explores beyond the native 60-second budget. It matches all 146 native
prefix laws and then reaches 164 laws. Its percentages describe that wider
profiling window. All nine optimized profile runs pass the common-prefix
check. PROFILING accounts for 11.5% to 24.4% of all self ticks in the eight
table rows. GC accounts for 0.7% to 6.7%. These costs are excluded from the
table denominator.

The four completed earlier-phase profiles match the native checkpoints
exactly: HugeLists5 has 91 laws after phase 1 and 106 after phase 2.
HugeLists6 has 130 and 149. The earlier phases spend a larger share on
input generation than the stalled phases. This difference would be lost
in a whole-process time profile.

The optimized Regex phase-1 profile assigns 84.1% of the remaining ticks to
completion and 14.5% to observation equality. Normalization accounts for
94.0% of completion ticks. Its hot paths match templates and types, check
type variables, compare terms and symbols, and check KBO decreases.
The equality paths compile and run NFAs. They do not construct the search
grammar. The profile reaches the same 26-law prefix as the native run.

HugeLists5 phase 3 has a different cost. Grammar reduction accounts for
94.0% of remaining ticks. Template pruning accounts for 1.1%.
[`subsumes`][cfta-subsumption] alone accounts for 50.8% in self ticks.
The observed path starts in `searchSpace` and `reducePartially`.
[Equality-class narrowing][cfta-narrowing] calls `mergeAlternatives`.
That operation uses structural subsumption to filter recursive alternatives.
It compares node pairs, scans alternatives, and checks their children.
This is not the template matcher. The profile reaches the same 149-law
prefix as the native run.

HugeLists6 phase 3 assigns 97.9% of remaining ticks to completion.
Normalization accounts for 91.7% of completion ticks. Structural term
equality contributes 38.8% of remaining ticks in normalization alone.
The largest equality paths pass through `matchTypeTerm` and `bindMatch`.
The profile reaches the same 164-law prefix as the native run.

HugeLists7 phase 1 has a mixed cost in the extended window. Completion
accounts for 40.4%, type and proof checks for 25.0%, and grammar and pruning
for 23.0%. Typed rewriting checks account for 23.7%. These include known-law
proofs and reducibility checks. Candidate type checking and compilation
account for 1.3%. Enumeration with suspended pruning accounts for 22.7%.
Grammar reduction itself accounts for only 0.09% in this window.
`matchPartial` contributes 5.5% in self ticks. Enumeration's `pure`, `state`,
and `(>>=)` contribute another 10.4%. The profile stops in size-7 `[A]`.
Input generation accounts for 7.1%.

Input generation accounts for 0.08%, 1.28%, and 0.08% of remaining ticks
in these Regex, HugeLists5, and HugeLists6 windows. These profiles do not
support input generation as their main optimization target.
They do not measure how much generation stronger templates could avoid.
The development Regex profile spends substantial time interning symbols.
That cost largely disappears in the optimized profile: `internSymbol` has
97 of 180,005 total self ticks. An `-O0` hotspot alone would give the wrong
priority for that change.

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

Fresh selected-runtime controls have these peak RSS values. The GHC process
includes the compiler and interpreter.

| Control | Native unchecked MiB | Native checked MiB | GHC MiB |
| --- | ---: | ---: | ---: |
| Lists5P4 | 50.5 | 52.5 | 531.0 |
| ListMonad6P4 | 77.7 | 81.8 | 531.9 |

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
   Current directed cases reject both recorded counterexamples. Neither
   these cases nor the larger random budget prove the surviving laws.

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
[diagnostic-source]: https://github.com/TharkunAB/cfta/tree/c47a1d8b1cd0799d4c3e3c6839dc82c3fd80444e/specftacular
[cfta-subsumption]: https://github.com/TharkunAB/cfta/blob/c47a1d8b1cd0799d4c3e3c6839dc82c3fd80444e/cfta/src/Data/CFTA/Interned/Operations.hs#L658
[cfta-narrowing]: https://github.com/TharkunAB/cfta/blob/c47a1d8b1cd0799d4c3e3c6839dc82c3fd80444e/cfta/src/Data/CFTA/Equality/Operations.hs#L238
[cfta-worklist]: https://github.com/TharkunAB/cfta/blob/d8e95efd0d5005a068bb6872cbcafb1dcd1030a4/cfta/src/Data/CFTA/Interned/Operations.hs#L658

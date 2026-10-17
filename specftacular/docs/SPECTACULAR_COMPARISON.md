# Spectacular and Specftacular

This report compares the published ICST 2023 Spectacular artifact with the
current Specftacular implementation. It reports elapsed time, allocation,
GC, peak RSS, and differences in the discovered laws. A larger law count
does not imply a better result. False and redundant laws increase the count.

Specftacular recovers the general `concat` laws and list-monad laws that the
port previously missed. Native checked execution, native unchecked execution,
and the GHC frontend produce the same laws in the selected controls. Sparse
evaluation reduces retained memory. It regenerates inputs when needed.
The machine has other activity, so elapsed times do not
establish a speed improvement. Several current workloads still reach the
time limit where the original artifact completes.

## Sources and method

The runs took place on 2026-10-17.

| Input | Revision |
| --- | --- |
| [Published Spectacular artifact](https://zenodo.org/records/7565003) | `00621f4f0f03e5d0afea3c730434a8842e473546` |
| [Current Specftacular](https://github.com/TharkunAB/cfta/tree/e27d61a9b686e3e29255b065f586df7bb7cb14dc/specftacular) | `e27d61a9` |
| [Published QuickSpec 2 benchmark artifact](https://zenodo.org/records/7565011) | Version 2.1.5, commit `967151eae493fa08a414386cdfb5ce7072477972` |
| [Extended ICST paper](https://mpg.is/papers/gissurarson2023spectacular-extended.pdf) | PDF SHA-256 `44fcc9a6c67a5ddefccb29c37ce721a354b427bc99d6a01dadbb5b9355535882` |

All 63 Haskell files in the Spectacular archive remain unchanged. Its ZIP
SHA-256 is `48ff8dc6671edd9636c3d2c44928aab80fd3c0f92cb56d380ece8a3ae0ca3fa0`.
The QuickSpec ZIP SHA-256 is
`3de3b0cb9c1411f81a329ea3a39b2be92c346bbdc4b5f61718f966ff930c3a91`.
QuickSpec 2 was not rerun. Its source and saved outputs provide reference
evidence.

The matrix executables were built from
`ce9327fbe055a5e91d17c1074173b5ce89356e17`.
A final lint cleanup uses `zipWithM` in two matcher expressions.
Rebuilding all five native benchmark executables produces identical
SHA-256 hashes. The matrix therefore measures the current optimized programs.
The frontend and memory controls also pass after that cleanup.

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

Both builds and all runs use `nix-shell`, `heavy-management`, and pueue.
The jobs run serially. Each job has a verified 16 GiB cgroup cap and no job
swap. Benchmarks use `+RTS -N1 -M6G -s -RTS`. Small controls use heap caps
of 2 to 4 GiB. These limits stay below the requested 80 GB maximum.

The matrix compares all 27 Table I configurations. The original measurements
come from the all-`-O2` baseline run. The final current build has a fresh run
of every configuration.
Each process has a 60-second timeout. The paper used 3600 seconds. Every
matrix result below comes from these new builds. Machine activity differs
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
| Lists | 7 | 2 | 1.07 | 21.6 | 32 | 0.53 | 21.5 | 16 |
| Lists | 7 | 3 | 18.11 | 70.8 | 73 | 11.74 | 81.6 | 34 |
| Lists | 7 | 4 | T | 139.5 | — | 27.59 | 192.3 | 48 |
| Octonions | 7 | 2 | 0.15 | 21.4 | 8 | 1.00 | 20.7 | 15 |
| Octonions | 7 | 3 | 0.17 | 20.1 | 8 | 1.01 | 20.5 | 15 |
| Octonions | 7 | 4 | 0.22 | 24.3 | 8 | 1.04 | 20.5 | 15 |
| Regex | 7 | 2 | 3.06 | 18.7 | 42 | T | 19.4 | — |
| Regex | 7 | 3 | 4.29 | 16.8 | 42 | T | 19.2 | — |
| Regex | 7 | 4 | 5.84 | 17.1 | 42 | T | 19.4 | — |
| ListMonad | 7 | 2 | 0.27 | 15.4 | 8 | 2.84 | 42.5 | 11 |
| ListMonad | 7 | 3 | 0.46 | 22.3 | 8 | 2.98 | 45.5 | 11 |
| ListMonad | 7 | 4 | 18.04 | 208.8 | 42 | 13.33 | 188.5 | 21 |
| HugeLists | 3 | 2 | 0.07 | 12.1 | 22 | 0.11 | 17.1 | 30 |
| HugeLists | 3 | 3 | 0.18 | 17.0 | 27 | 0.20 | 22.5 | 42 |
| HugeLists | 3 | 4 | 0.64 | 30.7 | 33 | 1.87 | 50.0 | 50 |
| HugeLists | 4 | 2 | 0.20 | 14.3 | 37 | 0.50 | 26.8 | 56 |
| HugeLists | 4 | 3 | 1.37 | 36.3 | 68 | 1.88 | 64.5 | 96 |
| HugeLists | 4 | 4 | 28.43 | 122.7 | 90 | 20.77 | 201.0 | 171 |
| HugeLists | 5 | 2 | 0.88 | 23.2 | 66 | 6.66 | 177.6 | 106 |
| HugeLists | 5 | 3 | 27.27 | 104.8 | 144 | T | 211.6 | — |
| HugeLists | 5 | 4 | T | 165.1 | — | T | 211.3 | — |
| HugeLists | 6 | 2 | 6.37 | 39.1 | 99 | 12.60 | 266.6 | 149 |
| HugeLists | 6 | 3 | T | 305.6 | — | T | 428.2 | — |
| HugeLists | 6 | 4 | T | 308.9 | — | T | 429.2 | — |
| HugeLists | 7 | 2 | T | 60.2 | — | T | 379.5 | — |
| HugeLists | 7 | 3 | T | 58.0 | — | T | 379.3 | — |
| HugeLists | 7 | 4 | T | 55.6 | — | T | 379.1 | — |

Spectacular completes 20 runs and reaches the limit in 7. Specftacular
completes 17 runs and reaches the limit in 10. No run has an unexpected exit
status.

Lists size 7 through phase 4 completes in Specftacular and reaches the limit
in the original. Regex size 7 through phases 2, 3, and 4 completes in the
original and reaches the limit in Specftacular. HugeLists size 5 through
phase 3 also completes only in the original. The HugeLists definitions differ
as stated above. Both implementations time out in the other six cells.

The current Lists7P4 run completes within the matrix limit. It prints 48 laws,
uses 192.3 MiB peak RSS, retains 62.1 MiB at the largest GC sample, and
allocates 121.39 GiB.

Selected completed runs have these costs:

| Signature, size, phase | Original allocation GiB | Specftacular allocation GiB | Original residency MiB | Specftacular residency MiB | Original GC CPU s | Specftacular GC CPU s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists-7-p2 | 4.275 | 3.456 | 5.35 | 2.98 | 0.231 | 0.032 |
| Octonions-7-p2 | 0.419 | 2.852 | 12.58 | 2.94 | 0.026 | 0.021 |
| ListMonad-7-p2 | 0.961 | 17.972 | 3.47 | 13.29 | 0.030 | 0.966 |
| ListMonad-7-p4 | 52.501 | 76.257 | 72.02 | 81.97 | 7.004 | 2.741 |
| HugeLists-4-p4 | 126.783 | 116.336 | 39.68 | 72.78 | 8.920 | 4.794 |
| HugeLists-6-p2 | 24.723 | 68.357 | 17.60 | 102.07 | 1.246 | 1.713 |

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
Repeated occurrences must agree. Smaller type sizes come first. Among
equal-sized types, abstract instances precede concrete instances during
exploration. This suppresses many ground consequences.
QuickSpec 2's [polymorphism layer][qs-poly] provides the design reference.

Lists5P4 produces the same 29 numbered laws in native checked execution,
native unchecked execution, and the GHC frontend. There are no exact
text duplicates after law numbers are removed. The normalized law text has
SHA-256 `528f224e2d6794e9ff6a73f97cd4a9218a71eb455c1a92fe0e5543ecba8b6f89`.
Both general laws are present:

```haskell
map f (concat xss) == concat (map (map f) xss)
concat xss ++ concat yss == concat (xss ++ yss)
```

The completed size-7 run also contains
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

The proof control checks all 63 equations of the previous size-7 Lists
output against the current 48-equation basis. All 63 follow, including the
15 equations that the stronger prover suppresses. A false concat/reverse
equation remains unproved. This is a software proof check, not an independent
formal verification or a proof that the basis is minimal.

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
execution, and GHC each produce the same 18 numbered laws. These include
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
build an exclusion product for every bucket. CFTA source remains unchanged.

A development Lists size-7 profile stopped after 300 seconds. It recorded
284,404,205 calls to `matchPartial` under newly started checks and 2,311,899
under resumed checks. Newly started checks account for 99.2% of those calls.
The current oracle indexes exact template heads
and application counts. It skips only incompatible fixed heads. Wildcards,
prefixes, and unknown heads retain the generic path. The index preserves
template order and duplicates. It does not change suspended matches.

A completed all-`-O2` control changes only this index. Lists size 7 through
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

A separate current Regex7P2 diagnostic with 100 random cases plus the same 40
validation cases also reaches the 60-second limit. It does not replace the
default-budget matrix cell.

## Memory and allocation

QuickSpec 2's sparse [decision tree][qs-tree] retains counterexamples that
separate representatives. The current engine follows that design. A leaf
retains a term evaluator. A branch retains one discriminator case and its
values. Test cases store seeds and boundary indexes. Each comparison generates
only the variables used by either term. Both evaluators use the same valuation
for that case. The tree retains a valuation only through discriminator values.
It does not retain all generated
nested lists and complete result vectors at every representative.

A fresh local control restores shared input maps and retained result vectors
in the current engine. It also restores the legacy decision tree's prefix
comparisons. It keeps the same pruning, proof shortcut, and available
validation cases. The strategies compare cases in different orders.
They can therefore treat partial values differently. This control compares
evaluation strategies, including storage. It does not isolate storage alone.
All variants produce the same 29 numbered Lists5P4 laws.

| Current Lists5P4 control, 1000 + 40 cases | Peak RSS, MiB | Allocated, GiB |
| --- | ---: | ---: |
| Shared inputs and retained result vectors | 1920.5 | 20.93 |
| Sparse evaluation | 51.4 | 20.59 |
| Sparse evaluation with native runtime checks | 54.2 | 21.36 |

The GHC Lists5P4 control uses 537.8 MiB peak RSS. That process includes
the compiler and interpreter. Its output agrees with both native modes.

Sparse evaluation regenerates inputs to reduce retained memory.
The sparse run uses 97.3% less peak RSS and allocates 1.6% less. Retaining the
complete input maps and result vectors restores the large peak. These
controls do not establish an isolated automaton speed improvement.

On Lists4P1, Cachegrind records 1,426,503,315 instructions for retained
vectors and 445,870,706 for sparse evaluation. RTS allocation is 521,257,520
and 178,430,168 bytes respectively. These are controls of the current source
with different evaluation strategies. They are not measurements of an earlier
port.

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
[original-node-oracle]: https://github.com/Tritlo/spectacular/blob/00621f4f0f03e5d0afea3c730434a8842e473546/spectacular/src/Spectacular.hs#L330
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

[qs-terms]: https://github.com/Tritlo/quickspec/blob/967151eae493fa08a414386cdfb5ce7072477972/src/QuickSpec/Internal/Explore/Terms.hs#L70

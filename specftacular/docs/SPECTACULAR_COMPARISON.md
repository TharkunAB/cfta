# Spectacular and Specftacular

The matrix compares the published ICST 2023 Spectacular artifact with
Specftacular at `d2e91fdf`. Separate controls and profiles cover the later
`09caaec3` fragment check. The report covers elapsed time, allocation, GC,
peak RSS, and differences in the discovered laws. A larger law count is not a
better result by itself. False and redundant equations increase the count.

The engine retains pruning during enumeration, increasing program size
order, occurrence generalization, and validated polymorphic schemes. Sparse
evaluation reduces retained inputs. Typed completion preserves rules across
type substitutions. The new 1064-case schedule rejects six additional false
equations at their actual admission identities. The previous 1040
Specftacular cases all passed for those equations. The GHC frontend uses the
same input policy.

The optional ordered CFTA cursor passes its API and default CFTA cost
controls. The Specftacular cursor variants fail their selection controls, so
the selected engine keeps its existing enumeration path. Those small default
controls do not establish the cost of larger Specftacular runs. Separate
profiles below identify the source of each run. Historical profiles and
rejected candidates retain their source labels.

The measured `d2e91fdf` runtime completes 22 of 27 configurations within
300 seconds.
The completed HugeLists size 7, phase 2 run has 242 laws. It omits six
concretely refuted equations from the earlier 248-law output. Printed
absence and bounded derivability checks have separate roles below.

## Sources and method

The original columns retain the earlier all-`-O2` measurements. Original
Spectacular and QuickSpec 2 are not rerun. The current matrix runs on
2026-10-18 with `d2e91fdf` and the 1064-case schedule. The matrix retains
those measurements. The later Spec-only callback controls do not replace
its timing, resource, or law-count rows.

| Input | Revision |
| --- | --- |
| [Published Spectacular artifact](https://zenodo.org/records/7565003) | `00621f4f0f03e5d0afea3c730434a8842e473546` |
| [Measured Specftacular matrix](https://github.com/TharkunAB/cfta/tree/d2e91fdf297659382329e8d9375082024439dc8c/specftacular) | `d2e91fdf` |
| [Spec-only fragment check](https://github.com/TharkunAB/cfta/commit/09caaec396a0e1f761a40cd7e218ecc6e8b5a518) | `09caaec3` |
| [Initial 1064-case input policy](https://github.com/TharkunAB/cfta/commit/54b17ac82e87e5ae6a15e640658058cf4d26bd6b) | `54b17ac8` |
| [Optional CFTA cursor](https://github.com/TharkunAB/cfta/commit/3cfd0ae71e92974640f6a386e91a9452735cd825) | `3cfd0ae7` |
| [Profiled 1040-case predecessor](https://github.com/TharkunAB/cfta/tree/102965d3bbffc564b79cb718b73b9f589f95f2ce/specftacular) | `102965d3` |
| [Published QuickSpec 2 benchmark artifact](https://zenodo.org/records/7565011) | Version 2.1.5, commit `967151eae493fa08a414386cdfb5ce7072477972` |
| [Extended ICST paper](https://mpg.is/papers/gissurarson2023spectacular-extended.pdf) | PDF SHA-256 `44fcc9a6c67a5ddefccb29c37ce721a354b427bc99d6a01dadbb5b9355535882` |

All 63 Haskell files in the Spectacular archive remain unchanged. Its ZIP
SHA-256 is
`48ff8dc6671edd9636c3d2c44928aab80fd3c0f92cb56d380ece8a3ae0ca3fa0`. The
QuickSpec ZIP SHA-256 is
`3de3b0cb9c1411f81a329ea3a39b2be92c346bbdc4b5f61718f966ff930c3a91`.
QuickSpec source and saved outputs provide reference evidence.

The host runs Ubuntu 24.04 under WSL2 on an AMD Ryzen 9 7950X. It exposes 24
logical CPUs and 94.29 GiB of RAM. Spectacular uses GHC 8.10.7 and
QuickCheck 2.14.2. Specftacular uses GHC 9.14.1 and QuickCheck 2.18.0.0.
Separate Cabal projects set `optimization: 2` globally and in `package *`.
Executables and Cabal-built dependencies use `-O2`. The original store audit
covers 53 external units. The selected d2e91fdf build passes fresh effective
`-O2` checks for all seven local components in each closure and 100/111
native/GHC external entries. These entries include build tools. The existing
checked and unchecked goldens pass. Native unchecked, native checked, and
GHC produce identical 24-law Lists size 5, phase 4 and 9-law Monad size 6,
phase 4 sequences. Physical alias probes pass. Compiler-distributed
libraries retain their toolchain settings. They are not rebuilt.

Builds and runs use `nix-shell`, `heavy-management`, and pueue. Jobs run
serially with a verified 16 GiB cgroup cap and no job swap. Benchmarks use
`+RTS -N1 -M6G -s -RTS`. These limits remain below the requested 80 GB
maximum. A preflight waits for low host load before measurements. It does
not reserve the host. Machine activity can change during a run, so
elapsed-time ratios do not isolate engine speed.

The matrix covers the 27 Table I configurations. Original runs have a
60-second limit. The fresh current base pass has a 300-second limit. A
900-second pass revisits unfinished searches under the recorded policy. The
paper used 3600 seconds. These different limits must remain explicit. A
same-size later phase can be inferred after an earlier-phase timeout at the
same limit. Such an entry has no independent cost or law-count measurement.
A user-policy skip is `NOT RUN`, not an inferred timeout. No inference
crosses maximum sizes. The longer pass retains completions only from this
same fresh current base pass.

Spectacular runs 100 fresh QuickCheck tests per comparison. Specftacular
uses 1000 shared random cases, eight separately seeded cases, 40 boundary
cases, and 16 predicate cases. All previous 1040 descriptors retain their
order and seeds. Compiler versions, signatures, generators, validation,
pruning, and enumeration differ. The comparison does not isolate automaton
cost.

GNU `time` reports peak RSS in KiB; tables convert it to MiB. RTS maximum
residency is live heap at GC samples, not RSS. Allocation is cumulative
traffic, not simultaneous RAM use. A timeout has no final law count. Its
buffered output can omit laws. Prefix counts include only newline-terminated
equations. A trailing fragment is not another law.

## Results

The original `T` means a 60-second timeout. A current `T` means a timeout at
the stated current limit. A dash means no final law count. HugeLists uses
different `usort` definitions: the original preserves duplicates, while the
current benchmark removes them. Its outputs are not identical workloads.

| Signature | Size | Through phase | Original s (60 s limit) | Original MiB | Original laws | Specftacular s (300 s limit) | Specftacular MiB | Specftacular laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists | 7 | 2 | 1.07 | 21.6 | 32 | 0.33 | 21.2 | 15 |
| Lists | 7 | 3 | 18.11 | 70.8 | 73 | 10.64 | 88.7 | 33 |
| Lists | 7 | 4 | T | 139.5 | — | 26.91 | 193.7 | 41 |
| Octonions | 7 | 2 | 0.15 | 21.4 | 8 | 0.92 | 20.8 | 15 |
| Octonions | 7 | 3 | 0.17 | 20.1 | 8 | 1.03 | 21.0 | 15 |
| Octonions | 7 | 4 | 0.22 | 24.3 | 8 | 0.99 | 21.0 | 15 |
| Regex | 7 | 2 | 3.06 | 18.7 | 42 | 54.66 | 47.6 | 60 |
| Regex | 7 | 3 | 4.29 | 16.8 | 42 | 52.38 | 48.1 | 60 |
| Regex | 7 | 4 | 5.84 | 17.1 | 42 | 56.36 | 48.5 | 60 |
| ListMonad | 7 | 2 | 0.27 | 15.4 | 8 | 3.63 | 42.9 | 9 |
| ListMonad | 7 | 3 | 0.46 | 22.3 | 8 | 3.83 | 42.8 | 9 |
| ListMonad | 7 | 4 | 18.04 | 208.8 | 42 | 7.25 | 187.8 | 9 |
| HugeLists | 3 | 2 | 0.07 | 12.1 | 22 | 0.10 | 16.9 | 28 |
| HugeLists | 3 | 3 | 0.18 | 17.0 | 27 | 0.20 | 22.6 | 40 |
| HugeLists | 3 | 4 | 0.64 | 30.7 | 33 | 1.89 | 48.1 | 46 |
| HugeLists | 4 | 2 | 0.20 | 14.3 | 37 | 0.51 | 26.7 | 46 |
| HugeLists | 4 | 3 | 1.37 | 36.3 | 68 | 1.77 | 69.7 | 84 |
| HugeLists | 4 | 4 | 28.43 | 122.7 | 90 | 14.29 | 156.7 | 125 |
| HugeLists | 5 | 2 | 0.88 | 23.2 | 66 | 6.73 | 183.4 | 92 |
| HugeLists | 5 | 3 | 27.27 | 104.8 | 144 | 36.72 | 519.5 | 197 |
| HugeLists | 5 | 4 | T | 165.1 | — | T | 819.5 | — |
| HugeLists | 6 | 2 | 6.37 | 39.1 | 99 | 11.84 | 252.7 | 130 |
| HugeLists | 6 | 3 | T | 305.6 | — | T | 613.6 | — |
| HugeLists | 6 | 4 | T | 308.9 | — | T (inferred) | — | — |
| HugeLists | 7 | 2 | T | 60.2 | — | 86.70 | 904.6 | 242 |
| HugeLists | 7 | 3 | T | 58.0 | — | NOT RUN | — | — |
| HugeLists | 7 | 4 | T | 55.6 | — | NOT RUN | — | — |

The retained original completes 20 runs and times out in seven. At 300
seconds: 22 new completions, 2 measured timeouts, 1 same-size inferred
timeout, 2 policy skips.

The completed-run costs remain mixed. Lists7P3 and HugeLists4P4 take less
elapsed time than the retained original runs. Regex and Octonions take more.
Regex7P2 allocates 399.451 GiB against the original 17.185 GiB, although its
peak RSS is only 47.6 MiB. HugeLists5P3 takes 36.72 seconds and 519.5 MiB,
against the original 27.27 seconds and 104.8 MiB. The larger test budget,
different equation bases, and changed workload meanings prevent an isolated
automaton-speed conclusion. The 22 current completions at 300 seconds and 20
original completions at 60 seconds are not a matched-budget advantage.

The resource table reports selected completed runs. Original reference
measurements remain unchanged.

| Signature, size, phase | Original allocation GiB | Specftacular allocation GiB | Original residency MiB | Specftacular residency MiB | Original GC CPU s | Specftacular GC CPU s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists-7-p2 | 4.275 | 1.975 | 5.35 | 2.54 | 0.231 | 0.027 |
| Octonions-7-p2 | 0.419 | 2.104 | 12.58 | 2.89 | 0.026 | 0.026 |
| Regex-7-p2 | 17.185 | 399.451 | 4.47 | 11.16 | 0.474 | 1.921 |
| ListMonad-7-p2 | 0.961 | 25.803 | 3.47 | 12.99 | 0.030 | 0.987 |
| ListMonad-7-p4 | 52.501 | 38.836 | 72.02 | 82.77 | 7.004 | 1.670 |
| HugeLists-4-p4 | 126.783 | 70.602 | 39.68 | 57.24 | 8.920 | 2.176 |
| HugeLists-6-p2 | 24.723 | 57.100 | 17.60 | 96.45 | 1.246 | 1.861 |

### Longer current-only trials

| Configuration | 900-second outcome | Measured seconds | Peak RSS MiB | Final laws | Visible complete prefix |
| --- | --- | ---: | ---: | ---: | ---: |
| HugeLists-5-p4 | T | 900.04 | 1078.4 | — | 281 |
| HugeLists-6-p3 | T | 900.00 | 689.9 | — | 170 |
| HugeLists-6-p4 | T (inferred) | — | — | — | — |
| HugeLists-7-p3 | NOT RUN | — | — | — | — |
| HugeLists-7-p4 | NOT RUN | — | — | — | — |

At 900 seconds: 0 new completions, 22 retained 300-second completions, 2
measured timeouts, 1 same-size inferred timeout, 2 policy skips. Only
same-source 300-second completions are retained. Timeout prefixes contain
complete lines only; buffered output can omit accepted laws. Inferred
timeouts and policy skips have no measured costs or law counts. No timeout
inference crosses maximum sizes.

Measured timeouts, same-size inferences, retained completions, and policy
skips are separate outcomes. Inferred or skipped rows have no measured RSS,
allocation, or law count. Timeout RSS and visible law prefixes remain
censored.

## Differences in laws

The fresh size-7 outputs contain 15, 33, and 41 Lists laws at phases 2, 3,
and 4. ListMonad prints nine laws in each phase. Regex prints 60 and
Octonions prints 15 in each phase. Each of these completed numbered streams
is identical to the corresponding `102965d3` 1040-case stream. This compares
printed bases. It does not prove equivalence of the complete search spaces
or validity of every law.

### Completed Regex runs expose more general equations

All three current completed phase bounds print the same 60 equations, with
general alternation commutativity at law 8, concatenation associativity at
law 25, and the two distribution laws at laws 58 and 59. The full numbered
streams match `102965d3`. The retained original has 42 equations and does
not print these three general commutativity and distribution equations. The
established Specftacular controls at `102965d3` include general alternation
commutativity and both distribution laws. With shorter names, these are:

```text
x | y == y | x
x ; (y | z) == (x ; y) | (x ; z)
(x | y) ; z == (x ; z) | (y ; z)
```

The retained original run prints commutativity instances with `any` and `e`.
It does not print these three general equations. Both runs print general
concatenation associativity. The original also prints seven associativity
instances with `any`. These examples compare the printed bases. Their counts
do not prove semantic coverage or independence. Regex equality checks
acceptance on 100 fixed words. It does not establish complete language
equivalence. The QuickSpec artifact has no saved Regex output, so it
supplies no measured law comparison for this workload.

### Boolean carriers admit false general laws

The original Lists7P2 run prints this equation, with variable names
simplified:

```haskell
map f xs == map f (map f (map f xs))
```

Set `f = succ :: Int -> Int` and `xs = [0]`. The two sides are `[1]` and
`[3]`. The original carrier types wrap `Data.Monoid.Any`, which contains a
`Bool`. Every total Boolean endomorphism satisfies `f^3 = f`. More tests
over that carrier cannot reject this equation. A historical fixed-seed
sample of 1000 original carrier values contains only two distinct values.
The integer carriers in Specftacular give 61 values in the corresponding
sample. The complete fresh Lists size-7 outputs at phases 2, 3, and 4 do not
print this form. The check permits consistent variable renaming and equation
reversal. It preserves displayed types and repeated variable identity. The
retained original Lists7P2 prints it as law 24. Printed absence does not
establish that current Rules cannot derive it. A finite sample does not
prove all surviving laws.

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
exploration. This suppresses many ground consequences. QuickSpec 2's
[polymorphism layer][qs-poly] provides the design reference.

Fresh Lists size 5 through phase 4 produces the same 24 numbered laws in
native checked execution, native unchecked execution, and the GHC frontend.
There are no exact text duplicates after law numbers are removed. The
normalized law text has SHA-256
`8088731afcad759c3a22db9f0c34a29b26b8d096115a55d19aa44a4850ec1821`. Both
general laws are present:

```haskell
map f (concat xss) == concat (map (map f) xss)
concat xss ++ concat yss == concat (xss ++ yss)
```

The selected size-5 control also contains `concat (concat xsss) == concat
(map concat xsss)`. It has no exact duplicate law text. These checks do not
establish a minimal or independent law basis.

### Completion and typed law coverage

Completion gives distinct names to each rule's term and type variables
before it computes an overlap. It unifies type constructors and rejects
cyclic substitutions. This permits overlaps such as `a := [b]` and `a :=
[[b]]`. A literal annotation comparison misses these consequences. For
example, double reverse, map/reverse, and a concat/reverse rule can prove:

```haskell
reverse (concat xss) == concat (reverse (map reverse xss))
```

Fresh all-`-O2` captures at `d2e91fdf` reproduce the selected 41-law Lists,
197-law HugeLists, and nine-law Monad outputs exactly. Their final Rules
derive 586 of 597 retained targets. The other 11 target occurrences have
independently checked counterexamples. The bounded prover returns no
derivation for those 11. No target is unproved without a counterexample,
unknown, or still derived despite its counterexample. All targets come from
retained Specftacular outputs. The six HugeLists size 7, phase 2 checks form
a separate control.

| Current control at `d2e91fdf` | Printed laws | Retained target corpora | Derived | Independently refuted |
| --- | ---: | --- | ---: | ---: |
| Lists7P4 | 41 | Exact typed 48-, 63-, and 41-law outputs | 152 | 0 |
| HugeLists5P3 | 197 | Earlier 214-law prefix and exact typed 204-law output | 407 | 11 |
| ListMonad6P4 | 9 | Earlier 18-law frontend output and exact typed nine-law output | 27 | 0 |

Printed-only targets lack constant annotations. Their reconstruction keeps
rigid given types and shared variable identities, freshens each constant
occurrence, and infers both sides jointly. It checks that policy against the
retained exactly typed targets. Exact typed targets retain their
annotations. The checker tries direct typed subsumption in both directions,
then normalization, with a two-second limit. It inserts no target and
performs no extra completion. Failed or timed-out proofs remain unknown
unless a separate concrete counterexample refutes that exact target.

The 11 refuted occurrences repeat seven HugeLists forms: two total-value
counterexamples and nine partial-context counterexamples. The bounded prover
returned no derivation for them. That does not prove non-derivability or
basis consistency. A false concat/reverse control also remained unproved;
`[[1],[2]]` supplies its concrete witness. A separate historical check at
`102965d3` derived the omitted zip-empty equation from its 125-law
HugeLists4P4 basis, with distinct rigid A/B carriers. These controls do not
establish equivalence of all 27 matrix bases. The Monad coverage control
uses size 6, not size 7.

Completion has an explicit annotation-depth budget. Program leaf count alone
does not bound type depth. The budget can omit valid critical pairs and does
not bound transient unification or normalization cost.

### Higher-order ListMonad coverage improves

The native resolver composes function generators from a `CoArbitrary` domain
and a generated codomain. It supports the `A -> [B]` variables required by
ListMonad. User overrides take priority in random generation. Function
values do not receive a fabricated `Eq` instance. Unsupported generator
types produce warnings. See QuickSpec 2's [generator
resolution][qs-generators].

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
does not print the exact Kleisli associativity equation from the saved
output. The applied Kleisli definition and bind associativity imply that
equation pointwise. Different equation bases need a derivability check;
their raw counts do not measure discovery quality.

### HugeLists uses duplicate-removing `usort`

The selected native and GHC definitions remove duplicates. Their focused
probes confirm `usort [1,1] == [1]`. For finite total lists, this supports
`usort (xs ++ xs) == usort xs`. The published duplicate-preserving
definition does not support that equation. This fixes a benchmark mismatch.
It does not make the measured original and current HugeLists signatures
identical.

### Directed cases reject the recorded false candidates

These two equations are false:

```haskell
take n xs == take n (take (n + n) xs)
length (take 1 (xs ++ ys)) == length (take 1 (zs ++ ys))
```

For the first equation, use `n = maxBound :: Int` and `xs = [0]`. Machine
integer addition gives `n + n == -2`. The sides are `[0]` and `[]`. For the
second, use `xs = [0]`, `ys = []`, and `zs = []`. The lengths are 1 and 0.

The directed schedule also addresses mixed Int-list values. For `x = 1` and
`xs = [0,maxBound]`, these sides have different total results:

```haskell
sort (map (+ x) xs) == map (+ x) (sort xs)
-- left: [minBound,1]; right: [1,minBound]
```

The duplicate-removing `usort` version fails in the same way. The retained
original HugeLists5P3 output prints the `sort` equation as law 133. The
[published signature][original-hugelist-signature] uses concrete `Int`.

`succ` has a different failure: it throws at `maxBound`. For `xs =
[0,maxBound]`, demanding the first element of `sort (map succ xs)` throws,
while the first element of `map succ (sort xs)` is 1. The `usort` version
has the same difference. At `xs = [maxBound]`, these three equations also
fail:

```haskell
map succ xs == map (+ 1) xs
succ (sum xs) == 1 + sum xs
sum (map succ xs) == sum (length xs : xs)
```

Demanding the left scalar or first list element throws. The corresponding
right result is `minBound`. These equations are unsafe as unconditional
rewrites under non-strict Haskell contexts. Full list equality can throw
rather than return `False`. The controls record that distinction. The
`102965d3` HugeLists5P3 output omitted all seven recorded forms. The
completed fresh HugeLists5P3 output has 197 laws and omits the two recorded
`take` forms and all seven recorded Int mapping, sorting, and `succ` forms.
The seven Int checks allow the same arbitrary list expression on both sides,
including `concat` expressions. The check for `(+ x)` retains the displayed
`x :: Int`. These are checks of printed syntax. They do not prove
nonderivability or reject every other false specialization.

### Six false equations and the input correction

The completed `102965d3` HugeLists size 7, phase 2 run printed the following
five false predicate equations. The numbers are its printed law numbers;
variable names are shortened.

| Law | Printed equation, with shorter names | Predicate |
| --- | --- | --- |
| 160 | `drop n (dropWhile p (takeWhile q xs)) == dropWhile p (drop n (takeWhile q xs))` | `p = (== 0)` |
| 167 | `drop n (filter p (takeWhile q xs)) == filter p (drop n (takeWhile q xs))` | `p = (== 1)` |
| 175 | `dropWhile p (take n (takeWhile q xs)) == take n (dropWhile p (takeWhile q xs))` | `p = (== 0)` |
| 178 | `filter p (take n (takeWhile q xs)) == take n (filter p (takeWhile q xs))` | `p = (== 1)` |
| 185 | `drop n (takeWhile p (takeWhile q xs)) == takeWhile p (drop n (takeWhile q xs))` | `p = (== 1)` |

For each equation, use `Int` for the abstract carrier. Set `n = 1`, `xs =
[0,1] :: [Int]`, and `q = const True`. The left side is `[]`; the right side
is `[1]`. These witnesses use total values and functions. They require no
overflow. An argument predicate can distinguish values even when the list
operations are parametric.

Law 208 has a separate overflow counterexample:

```haskell
drop n (drop n (drop n xs)) == drop (n + (n + n)) xs
```

Set `n = div maxBound 2 + 1 :: Int` and `xs = [0]`. On the 64-bit host, `n`
is 4611686018427387904. The sum on the right wraps to −4611686018427387904.
The left side is `[]`; the right side is `[0]`.

The original focused Haskell control checks laws 160, 167, 175, 178, and
208. An exact admission capture records their types and actual variable
identities. Both original and post-generalization terms pass all 1040 old
cases in checked and unchecked execution. Ordinary decision-tree insertion
equates every pair. There are no exception observations. Generalization
leaves these five equations unchanged. That first control covered five
equations. The current all-`-O2` control below also checks law 185.

Generation seeds include variable names. Replaying the canonically printed
names gives a different sample and refutes the first four equations in 3, 6,
4, and 6 random cases. That replay does not reproduce admission. The capture
resolves the discrepancy: the actual admission identities expose a finite
sampling gap. It provides no evidence of skipped validation for these
events.

The selected schedule retains all 1040 previous cases and appends 24:

- Sixteen predicate cases use `n = 1` and exact typed lists `[zero, one]` for
  Int, A, B, C, D, and Acc. One predicate-index residue modulo eight receives
  equality with zero or one. Other predicates return True. This covers each
  ordered pair with different residues, independently of variable names and
  list indexes. It does not guarantee coverage when distinct indexes share
  a residue. Unsupported types use their generators with separate seeds and
  size zero.
- Eight boundary cases use `maxBound div 2 + 1` and `minBound div 2 - 1`, each
  at four list-presence slots. They expose both signs of wrapped triple
  addition. They reuse the existing exact typed boundary-value policy.
  Unsupported types use their generators at size zero in these eight cases.

For laws 160, 167, 175, 178, and 208, the new 24 cases refute the original
and final equations at their actual captured identities in both native
modes. Full-schedule and tail-only decision trees distinguish all 20
law/version/mode combinations. All old 1040 results remain True, and no new
observation throws. Separate controls cover all six domains and all 56
ordered index pairs from zero through seven. All 17 focused check groups
pass. Typed sentinel generators confirm the old 1040 values and all seeds
remain unchanged. They also confirm size zero for unsupported types in every
new case. GHC physical alias probes reject the predicate and both half-range
witnesses. The GHC Monad size 6, phase 4 control retains its exact nine-law
sequence. These correctness probes compile the current HOME modules at `-O0`
against audited `-O2` dependencies. They support no timing claim.

The fresh 242-law output is exactly the old 248-law stream with laws 160,
167, 175, 178, 185, and 208 removed. It has no added equations or changes to
the remaining equation order. Law 185 has actual predicate indexes zero and
one. `PredicateCase 0 1` supplies its stated witness. The focused check
below uses its exact captured names.

A fresh all-`-O2` capture reproduces the 242-law output exactly. The checker
uses only its final Rules. All 12 typed original/final queries for the six
refuted equations return `NOT-PROVED` within the two-second per-query bound.
None throws or times out. The checker proves the append-empty identity by
direct typed subsumption and does not prove the false concat/reverse
control. It inserts no target and performs no extra completion.

Actual-name replay checks 72 combinations of equation, version, evaluation
mode, and schedule group. Every old 1040-case observation is True for all
six equations, and each old-schedule decision tree returns `EqualTo`. Law
185's old results are measured without an assumed pass. Both the new 24
cases and the full 1064-case schedule give `Distinct` for all 24
equation/version/mode combinations. Checked and unchecked counts agree. No
observation throws. These replays expose a finite input gap. They do not
identify the original search's exact admission path.

A successful bounded negative check is not proof of non-derivability. These
controls do not validate every equation in the previous 248-law basis. This
is a correction to Specftacular's input policy, not a new paper erratum.

The earlier 32 boundary cases remain unchanged. Selected concrete Int lists
contain `[0,boundary]` at the extrema, including the innermost lists in the
two supported nested Int-list types. Other direct boundary lists retain
their single-zero or empty values. In those original cases, unsupported
lists use their generators at size zero in inactive slots and size 100 in
active slots. The 24 new cases request size zero for every unsupported type.
A custom generator can ignore this request. A typed sentinel control returns
a nonempty nested list at size zero. Thus, the size request does not
establish emptiness or a memory bound. Presence slots use indexes modulo
four.

`SPECFTACULAR_TESTS` still counts only random cases. The default total is
now 1064. Directed values can fall outside a custom generator's domain.
Logical type lookup prevents concrete Int values from replacing abstract
carrier values. Finite testing can still admit false laws that affect later
pruning.

### Representative instances change the equation basis

With the same nonnegative-integer gcd signature and term size 3, the
original prints 22 laws. The current golden prints six. The paper describes
generalizing discovered laws. The current search also tests instances of new
representatives. These six laws include general commutativity, idempotence,
the zero identity, and three constant reductions. The original gives
commutativity only at the supplied constants 1029, 1071, and 21. Fewer laws
give a more general result in this example.

The original Octonions size 7, phase 2 output prints eight laws. The saved
QuickSpec output has 15. The established Specftacular controls include
flexibility and three Moufang forms absent from the original output. Each
completed fresh size-7 run prints the same 15 equations as `102965d3`.
Flexibility is law 8. The middle, left, and right Moufang forms are laws 11,
14, and 15. None of these four displayed forms occurs in the retained
original eight-law basis. The saved QuickSpec artifact also has 15
equations; equal counts do not establish equivalent bases.

The paper already explains this kind of difference. Section IV-A,
“Differences in Discovered Laws”, describes QuickSpec's schema heuristics
and their effect on Octonion laws. A different basis or orientation is not
itself an error. See QuickSpec 2's [schema layer][qs-schemas].

## Enumeration and pruning

Phase order follows paper section III-C. Each phase visits increasing
program leaf sizes, then type buckets ordered by type size. Abstract
carriers precede concrete types of equal size. Knuth-Bendix order resolves
order within a bucket. Rules pass to later phases. Occurrence generalization
remains in place as in section III-G: the grammar uses one variable per
type, then tests independent assignments, with more general instances first.
A repeated-variable schema is not proof of every renamed equation. New
representatives through five leaves also receive instances, following
[QuickSpec 2][qs-schemas]. Instance enumeration uses up to four names per
type; the initial most general instance can use more.

The partial-term oracle follows section III-D. It suspends a match at an
unresolved subterm and resumes it when that subterm expands. A proven match
rejects the branch before the remaining choices expand. The selected search
therefore prunes during enumeration. It does not use the published node
oracle that the artifact source marks as too strong.

Each size/type bucket takes a template snapshot. The final KBO sort demands
the candidate bucket before its first test. Laws learned in that bucket can
change complete-candidate checks, but they cannot change enumeration already
performed under its snapshot. Paper section III-E describes size/type
batching. A fully online ordered extractor is an extension to this strategy,
not evidence that the paper's algorithm required a different implementation.

Early templates are linear, well typed, and decreasing. Repeated term
variables cannot become independent holes. Type erasure requires
principal-type coverage and a decrease independent of annotations.
Otherwise, annotations stay exact. The template-head index skips only
incompatible fixed heads and application counts. Wildcards and unknown heads
retain the generic path. Template order, duplicates, and suspended checks
remain intact. Empty pending sets avoid partial reconstruction only when the
concrete root cannot start a match.

Complete typed rewriting can use nonlinear rules before value generation.
Schema and instance trees first check whether existing rules prove equality,
as [QuickSpec 2][qs-terms] also does. New equalities still use the full test
schedule. Ordinary equality exceptions discard a candidate; cancellation and
timeouts propagate.

Parametricity permits reuse across type instances only when signature
constants are parametric in the abstract carriers. They must not inspect
their runtime representation or capture class dictionaries. Concrete
arithmetic types stay rigid. Typed rewriting applies an accepted scheme
through a shared substitution. Stronger independent binders need the
separate validation described below.

## Completion improvements

Completion rejects incompatible program shapes before typed matching. It
caches normal forms while the rule set stays fixed. Each accepted equation
starts a new cache. Cache keys include all annotations and use structural
equality. The cache holds at most 256 entries. Each key and value has at
most 256 term nodes, including annotations. Larger terms normalize without
cache insertion. The size check runs before hashing. It forces each accepted
node and symbol to weak head normal form without forcing symbol payloads.
Cache updates are forced between pairs. Keys and values contain at most
131,072 expanded node occurrences; this does not bound heap bytes. These
limits prevent the large retained terms seen with the rejected unbounded
cache.

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

The rewriter fixes a defect in the port's rule classification. The previous
classification used an order that could depend on symbolic type annotations.
Renaming or instantiating those types could reverse the order. Keeping only
the first direction then omitted a valid rewrite in another instance.

A captured HugeLists completion demonstrates the consequence. After 10,000
critical-pair steps, 54 added index entries contain only nine distinct
canonical typed equations. The first repeated equation is not subsumed in
its forward direction, although an existing reverse rule proves it with the
actual typed matcher. Canonical renaming then recreates a direction already
in the index. This repeats completion work.

The corrected classification uses `annotationIndependentGreater`. A single
direction requires a decrease that survives shared term and type
substitution. Otherwise, the index retains both directions. Each actual
rewrite still checks the instantiated order. A direction with unbound
right-side variables cannot invent bindings. The proof assumes finite,
well-formed typed terms and separate term and type variable namespaces. The
conservative fallback can create more critical pairs.

Completion must also preserve the type instances of a critical pair. Its
normalization now uses only decreases that hold for every type instance. An
order based on the current symbolic annotations can make a generic pair look
redundant while another instance still needs its equation. Storing both
directions does not repair a pair already discarded by normalization.

The ground-joinability shortcut now requires closed type annotations. Its
term-variable orderings do not cover changes to type-variable order. A pair
with unresolved type variables keeps the ordinary typed checks and
completion path. The existing program-size, annotation-depth, and
term-variable-order budgets remain. These conservative conditions can retain
more equations. They do not prove that completion finishes.

A small typed witness compares `length (fst ([], []))` with `length (snd
([], []))`, with independent list element types. Both values are zero.
Swapping the element types changes the old order. The corrected rules handle
both orders. Fifteen initial and 44 additional checks cover alpha renaming,
concrete `Int` and `Bool` instances, compound types, stable one-way rules,
and unbound right-side variables. The false concat/reverse control remains
unproved. These checks support the rule-classification contract. They do not
prove completion or confluence for every signature. This is a correction to
Specftacular's rewriter. The paper does not specify this
annotation-sensitive classification, so it is not a new paper erratum.

### Share critical-pair inputs within each batch

The selected rewriter computes the incoming rule's fresh names and left
contexts once per batch. It reuses those terms while visiting the existing
rules. It keeps the original binder names, rule order, overlap order, and
FIFO queue. The change adds no persistent cache.

An all-O2 replay processes the same 10,000 critical pairs before and after
this isolated sharing change. The interval still has pending pairs. Both
runs produce the same 1,066-entry typed snapshot, with identical index
classes, order, and binder names. Sampled allocation in that interval falls
from 10,717,798,480 to 9,679,273,104 bytes, a reduction of 9.690%. Source
inspection preserves the ordered pair stream; the replay directly checks its
final snapshot and step count.

A separate complete HugeLists5P3 control prints the same 204 laws in the
same order. Its whole-process allocation falls by 0.394%. The host is noisy,
and one pair does not establish a timing improvement. The larger replay
reduction applies to its selected completion interval. It does not describe
the whole search. These controls precede the current 1064-case policy. They
do not measure the selected matrix or establish a whole-search timing
improvement.

## Structural reduction and equation generalization

A historical optimized profile of `456123af` assigned 85.4% of application
ticks to structural subsumption, excluding GC and PROFILING. A captured
query visited 13,551,744 node pairs recursively, but only 29 distinct
ordered pairs. The [CFTA worklist][cfta-worklist] checks each mandatory pair
once per query. One compatible unconstrained wider edge makes its child
pairs mandatory. Zero compatible edges reject the query. Multiple edges
restart the original traversal. Empty/equal-node shortcuts remain. This
assumes finite, total, immutable closed graphs and valid node identities.
The visited set can reach the product of graph sizes. It remains a
sufficient structural test, not complete language inclusion.

A separate historical completion capture explains why independent type
schemes matter. All 178 additions specialize one equation:

```haskell
length (take (length xs) ys) == length (take (length ys) xs)
-- xs :: [a], ys :: [b]
```

The earlier scheme required the same element type for both lists. The
validated independent scheme subsumes those additions. Injecting it into the
captured queue lets that queue finish after 73 steps without new rules. The
diagnostic adds no overlaps for the injected rule, so it does not establish
theory closure. This motivates earlier generalization, rather than faster
evaluation of every specialized consequence.

[QuickSpec 2's regeneralise method][qs-regeneralise] supplies the inference
approach. Specftacular keeps variable identity across both sides and freshens
constant occurrences while preserving shared binders within each occurrence.
Given instances keep their declared types. One shared match must recover both
original sides. Concrete constructors remain fixed; an entire variable type
cannot simply become a fresh type variable.

Typing alone does not accept a proposal. Independent binders receive
distinct carriers from A through Acc. Each term variable receives a fresh
generator at its inferred type. Both sides must compile at the original
result type. Validation uses the actual supplied equality and the full
1064-case schedule. False, untestable, unsupported, or changed-result
proposals retain the original law. Cancellation and type errors propagate.
Generated values are not retagged.

## Validation costs and default API behavior

The optional cursor and the input policy are separate changes. Strict cursor
controls pass. The existing CFTA suite passes 741 examples in both
validation builds. All eight default allocation/instruction cells retain
their checksums and pass the 5% budget. Their largest increases are
0.000175% allocation and 0.000467% instructions. These controls check the
existing default CFTA path. They do not show that the Specftacular cursor
variants improve search.

At d2e91fdf, the all-`-O2` Lists size 4, phase 1 control retains all 10
laws. Allocation changes by +0.732441% and Cachegrind instructions by
+0.436728% against 102965d3. Both pass the 5% gate. The directed input
domain differs; no timing or isolated engine-speed claim follows.

Matched all-`-O2` Lists size 7, phase 4 controls isolate the larger
allocation change. Every variant completes with the exact same 41-law
sequence.

| Variant | Allocated bytes | Change from the 1040-case baseline |
| --- | ---: | ---: |
| Original 1040-case runtime | 108,513,645,280 | — |
| Optional CFTA API with the same 1040 cases | 108,553,232,800 | +0.0364816% |
| Optional API with the initial 1064 cases | 135,131,945,336 | +24.52991% |
| Selected 1064 cases with small unsupported inputs | 108,560,902,512 | +0.0435496% |

The selected change retains every descriptor, seed, and direct typed value.
It requests generator size zero only for unsupported types in the new 24
cases. That change reduces allocation by 19.6630% against the initial
1064-case implementation. The final increment over the API-only 1040 control
is 0.0070654%. These controls identify the added fallback inputs as the
source of the large allocation increase in this workload. They required no
further CFTA change. Other Lean work ran on the host, so no elapsed-time or
CPU-time ratio is selected from these allocation controls.

The earlier generalization change at `9be187a0` remains a separate accepted
exception against `456123af`: +15.826% allocation and +17.002% instructions
on Lists size 4, phase 1. Its ten program equations include stronger
independent carrier schemes; setting B = A recovers the earlier forms. That
change exceeded the 5% gate. The smaller new increment does not remove that
cost or establish a universal speedup.

## Profiles of the 1040-case predecessor

These diagnostics measure `102965d3`, not the selected 1064-case runtime. A
native trace records the actual phase and size/type boundaries. Its native
driver uses the retained O2 runtime and libraries. It adds line buffering
and phase/bucket logging. It keeps the search, 1040-case schedule, N1, 6 GiB
heap cap, and 16 GiB process-group cap. The 900-second size-5 trace agrees
with all 281 complete numbered lines in the corresponding timing output. It
captures 295 complete lines in total. Different interrupted prefix lengths
do not establish equal work.

| HugeLists maximum size | Phase 1 CPU s | Phase 2 CPU s | Phase 3 CPU s | Phase 4 CPU s | Actual terminal bucket |
| --- | ---: | ---: | ---: | ---: | --- |
| 5 | 5.86 | 0.82 | 29.92 | 864.80, interrupted | Phase 4, size 5 `[[Int]]` |
| 6 | 9.72 | 1.52 | 890.28, interrupted | Not reached | Phase 3, size 6 `Int` |

These CPU intervals include GC. The phase intervals do not overlap. Bucket
intervals nest inside them and must not be added to phase totals. For
maximum size 5, about 96% of observed CPU time is in phase 4. Its largest
completed bucket is size 5 `[[B]]`, at 105.55 CPU seconds. That bucket
starts after 588.88 elapsed seconds. The terminal `[[Int]]` bucket has
102.19 observed CPU seconds. Several earlier size-5 list buckets take 65 to
79 CPU seconds each. The cost is distributed over several type buckets. It
is not one late operation whose removal would eliminate the whole phase.

For maximum size 6, phases 1 and 2 finish in 11.240 CPU seconds. The phase-3
size-5 `Int` bucket completes in 20.674 CPU seconds. The later size-6 `Int`
bucket uses 848.259 CPU seconds before interruption. Its sampled allocation
is 5504.298 GiB. This is cumulative allocation, not RAM held at once. The
requested phase 4 is never reached.

The size-6 trace prints 223 complete laws. All 170 complete lines from the
900-second size-6 phase-3 timing output match its ordered prefix. The timing
output ends with a partial next line; the diagnostic uses line buffering.
The extra visible laws do not establish more completed work. All started
diagnostic intervals have end or abort markers. Neither trace has malformed
events. Their actual terminal buckets differ, so one explanation cannot be
assumed for both.

The diagnostic also records sampled allocation and GC endpoints. These
measure cumulative traffic, not retained memory. Phase boundaries alone do
not separate enumeration, completion, schema assignments, or test values.
Cost-centre observations must identify the window they actually reached.

### Late cost-centre controls at `102965d3`

Early automatic cost centres changed the search cost substantially. A
600-second profile did not reach the selected phase-4 `[[B]]` bucket. It
recorded zero gated CPU samples. Its earlier phase-3 size-5 `Int` bucket
took 345.59 elapsed seconds, versus 18.09 seconds in the native trace. Its
allocation totals cover the prefix that ran. They do not attribute the
unreached bucket. A brief second attempt was stopped and excluded.

The replacement build uses GHC's
[`-fprof-late`](https://downloads.haskell.org/ghc/9.14.1/docs/users_guide/profiling.html#ghc-flag-fprof-late).
GHC inserts these cost centres after Core optimization. The build compiles
all 20 reached CFTA modules, seven Specftacular modules, and the driver at
O2. It disables early automatic and manual cost centres. It reuses the
audited external O2 profiling libraries. It links no archived CFTA or
Specftacular library in place of these source modules.

A completed HugeLists5P3 control prints the exact retained 197 laws in
order. It takes 135.58 seconds, versus the retained native 37.33 seconds.
This 3.63-fold ratio measures distortion on that one control. It is not a
correction factor for later profiles. The phase and bucket logging also
remains enabled in these diagnostics.

The selected windows are phase 4, size 5, `Int` for maximum size 5, and
phase 3, size 6, `Int` for maximum size 6. Each window has a 180-second
limit. A 900-second whole-run guard also includes the prefix. Only timer
samples inside the reached window describe its CPU costs. Allocation and
entry counts cover the whole process. Each raw cost-centre self cost is
counted once. Inherited totals overlap and are not added. Source locations
and stack context support the category assignments. Inlining can move costs
to a caller or a compiler worker. Unclassified costs remain explicit.

The maximum-size-5 window completes its phase-4 size-5 `Int` bucket. It
records 156,508 samples and preserves the first 234 complete laws from the
native trace. This completes one bucket, not the HugeLists5P4 search. The
maximum-size-6 window reaches its 180-second limit inside phase 3, size 6,
`Int`. It records 181,902 samples. It preserves the native trace's 223
complete laws and prints no further law during this window. Its whole-run
guard does not interrupt the selected window.

After excluding GC, PROFILING, SYSTEM, and IDLE, the size-5 window has
135,525 application samples. The size-6 window has 129,097:

| Work | Size-5 samples | Share | Size-6 samples | Share |
| --- | ---: | ---: | ---: | ---: |
| Enumeration and template pruning | 128317 | 94.68% | 127335 | 98.64% |
| Typed eligibility and known proofs | 4173 | 3.08% | 50 | 0.04% |
| Generated inputs | 1197 | 0.88% | 0 | 0.00% |
| Evaluation | 326 | 0.24% | 0 | 0.00% |
| Equality | 78 | 0.06% | 0 | 0.00% |
| Decision-tree navigation | 134 | 0.10% | 0 | 0.00% |
| Completion | 20 | 0.01% | 0 | 0.00% |
| Other | 1280 | 0.94% | 1712 | 1.33% |

GC accounts for 2.66% and 20.02% of all samples, respectively. PROFILING
accounts for 10.01% and 8.37%. SYSTEM accounts for 0.74% and 0.64%. These
shares describe instrumented windows, not native GC costs. The named
`matchPartial` function alone accounts for 24.43% and 24.61% of application
samples. Other hot centres are CFTA enumeration workers, UVar updates,
partial-term expansion, and intersection. These observations support earlier
template rejection and less repeated matching. They do not support
completion or QuickCheck optimization as the first change for these two
windows. Zero samples do not prove zero execution time.

### Earlier profiles that guided completion changes

The first two profiles measure `9be187a0`, before the orientation and
sharing changes. The third measures `dd5da750`, before type-uniform
completion. They identify the work that led to the selected changes. They
measure neither `102965d3` nor the selected 1064-case distribution. All
local modules, CFTA, and external Cabal dependencies use O2.

Native diagnostics record actual phase and size/type bucket boundaries. The
through-phase setting only stops execution at a phase boundary. A later
requested phase therefore shares the earlier ordered search prefix for the
same size. This does not make separate timing samples interchangeable. Only
complete, newline-terminated equations count as captured output. A timeout
can leave buffered equations and a trailing fragment.

The [cost-centre timer][ghc-profile-timer] starts at the selected bucket.
Each window lasts up to 180 seconds. The denominator below excludes GC and
PROFILING self ticks. It retains SYSTEM and IDLE. Each self tick is assigned
once. Attribution uses [source paths][ghc-costs] and explicit
value-operation corrections for lazy construction ancestry. It remains a
source-based interpretation.

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

The size-6 profile reaches its 180-second limit in completion. Normalization
uses 64.55% of application/runtime ticks, critical-pair generation 28.63%,
and ground joinability 3.96%. Enumeration and pruning use 0.65%. A captured
10,000-step completion adds 226 distinct typed entries. Of these, 222 share
this erased equation family:

```haskell
length (take (length xs) (sort ys)) == length (take (length xs) ys)
-- xs :: [a], ys :: [Int]
```

Joint renaming of term and type binders reveals no increase in duplicate
entries. Exact duplicate suppression does not address this measured growth.
A focused probe uses actual critical pairs from the captured rules. The old
normalizer discards a generic pair as equal, but a closed type instance
still needs the equation under the same Rules. Uniform normalization retains
the pair. The old ground-joinability shortcut would then discard it again.
Both corrections are necessary for this witness. All 16 typed probe reports
complete, and both false concat/reverse controls remain unproved.

Only ticks belong to the selected timer windows. Profile allocation and
entry counts include the preceding search. No profile finishes its selected
bucket. Their elapsed times cannot supply a completed-work speed ratio.
Their differing costs also rule out one explanation for every HugeLists
timeout.

## Ordered enumeration controls

These isolated controls use runtime `102965d3` with the previous 1040-case
schedule and the stated enumeration changes. They do not supply the new
current matrix columns. All reached CFTA and Specftacular modules and
dependencies use `-O2`. Each run uses N1, a 6 GiB heap cap, and a verified
16 GiB cgroup with no swap. Original Spectacular is not rerun.

The complete reference is HugeLists size 5 through phase 3, with 197 laws.
Both shallow variants produce that exact sequence. They allocate 77.3% and
189.2% more than the paired eager control. Both are rejected.

| Variant | Result | Laws or prefix | Wall s | CPU s | Allocation GiB | Peak RSS MiB |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Eager control | Complete | 197 | 39.45 | 39.50 | 210.476 | 522.1 |
| Shallow children | Complete | 197 | 62.16 | 62.25 | 373.218 | 527.9 |
| Shallow with program hints | Complete | 197 | 100.88 | 101.02 | 608.757 | 530.4 |
| Ordered, weak program bound | Frontier limit | 133 | 50.32 | 50.39 | 242.597 | 424.5 |
| Ordered, program-shape bound | Frontier limit | 133 | 116.59 | 116.75 | 528.672 | 991.0 |
| Ordered, incremental key hints | Frontier limit | 133 | 41.07 | 41.12 | 191.324 | 889.1 |

The ordered variants reach the 100,000-entry frontier limit in phase 3, size
5, Int. All preserve the same 133-law prefix. None finishes the bucket. They
stop with different pending work, so their ratios are not speedups for the
same completed work. The cap stays fixed. No size 6 trial follows these
failed size 5 controls. Specftacular keeps its existing enumeration path.

The CFTA ordered cursor is an optional API. A caller must supply a fixed
complete key, a valid lower bound for partial terms, monotone pruning
callbacks, and a ready-hole preference. The cursor rechecks queued work
against the current pruning state. Work and frontier limits retain pending
work. Equal-key order can change. Residual obligations retain multiplicity,
but their list order can change. The CFTA documentation states the callback,
bound, and cyclic-truncation contracts. Queue capacity does not bound RSS or
the memory retained by closures. Specftacular does not select this cursor.

### Cost-centre evidence for the rejected ordered control

A separate all-`-O2` late-SCC build profiles the program-shape-bound
variant. The selected window samples 180.06 CPU seconds in phase 3, size 5,
Int. All 133 preceding laws match the native control. No law appears in the
window. Allocation and entry totals include the preceding search. They are
not totals for this window.

The application denominator is 160,646 ticks. It excludes GC, profiling,
SYSTEM, and IDLE. Enumeration and pruning account for 160,294 ticks
(99.78%). The main exclusive shares are 53.60% enumeration state, 25.77%
exact or annotation keys, 10.33% queue operations, 6.50% scheduling, 3.02%
pruning, and 0.41% shallow expansion. These subcategories are not an
exhaustive list. Generated inputs, evaluation, value equality, decision-tree
navigation, and completion each have zero sampled ticks. GC accounts for
4.81% of all 180,058 samples. Profiling overhead accounts for 5.33% of that
same total.

The sampled `poly_go3` worker has no source location. Its exact operation
remains unknown. Grouping does not show that every state tick traverses a
partial root. A Lists size 4, phase 1 pilot retains all 10 laws. Native wall
and CPU times are 0.05 and 0.04 seconds; profiled times are 0.25 and 0.25.
This shows instrumentation cost. It gives no conversion factor for the large
sampled bucket.

A separate priority diagnostic records 3,162,483 hole selections in the Int
bucket. Type-key hints account for 2,959,692 (93.59%). Pending type or other
checks account for 168,069 (5.31%). Pending program checks account for
34,720 (1.10%). There are two program-key selections and no fallback
selections. The maximum hint list has 26 entries. These are demanded
selections, not counts of invalid type instances. The selector can skip
blocked hints, so zero fallbacks does not show that all earlier hints were
ready. The priority change took effect but did not prevent the frontier
limit.

### HugeLists bucket statistics for `d2e91fdf`

A separate all-`-O2` diagnostic uses `d2e91fdf` at actual phase 3,
program-leaf size 5, and result type `Int`. It preserves the earlier search.
The 133-law entry prefix matches the fresh matrix. The hook runs after
reduction and refold, before the full KBO sort. It tests no term and admits
no law in that bucket.

After graph observation, the diagnostic inspects 512 unpruned accepting
runs. It keeps rigid Given names and declared types in each program shape.
It preserves separate constant occurrences, raw annotations, and residual
obligations. This traversal sample is not a KBO prefix.

| Observed sample metric | Count |
| --- | ---: |
| Entry templates | 173 |
| Raw accepting runs | 512 |
| Distinct annotated terms | 512 |
| Distinct program shapes with rigid Givens | 512 |
| Invalid typed terms or residual obligations | 0 |
| Runs matched by at least one entry template | 290 |
| Templates matched in the sample | 23 |
| Template/run match incidences, including overlaps | 434 |
| Uncovered runs and uncovered shapes | 222 |
| Expanded program nodes | 4608 |
| Expanded canonical annotation nodes | 18412 |

There are 43 raw records with the `Mu` recursion marker. The current
annotation parser maps a raw `Mu` leaf to carrier `A` before canonical type
checking. These observations retain that cutoff policy. They do not prove
correspondence with an unrestricted recursive language. The probe does not
compile or evaluate the records.

Each observed program shape has one canonical annotation witness. This
sample does not establish repeated complete witnesses for a fixed program.
Annotations account for 79.98% of its expanded term nodes. This is a
structural count, not a CPU share. The graph observation exhausts 266
references and 683 reference edges. Its 267 role visits comprise 47 program,
219 annotation, and one marker visit. A reference can have more than one
role. These counts do not measure enumeration-state visits.

A control uses the same phase grammar at leaf size 2 and the size-5 entry
templates. It exhausts all 18 raw runs. Direct template filtering and the
actual pruner keep the same 16 annotated runs with the same multiplicities.
Their canonical KBO streams also match. Every control run has no residual
obligation. This verifies the local measurement method on that finite
language.

The large sample does not exhaust the size-5 language. The existing oracle
already uses its entry templates. The 290 matches therefore do not measure
additional pruning that a compiled recognizer could provide. The sample
also omits `seen` and complete-candidate reducibility checks. A full
optimization decision needs counts of failed partial type choices and
annotation-state work. The next diagnostics measure those events.

### Default-pruner demand counts for `d2e91fdf`

Two diagnostics use `d2e91fdf`, the full 1064-case schedule, and one O2
counter binary. Counters start after reduction and refold. They stop after
the first sorted candidate-list demand, before the selected bucket's tests.
The size-5 control then completes with the exact current 197-law sequence.
The size-6 control stops after a 30-second window in phase 3, size 6, `Int`.
It prints 223 complete equations before that bucket's tests. All 24,576
retained native output bytes match its prefix, including the fragment of
equation 171. Buffered output does not identify the native stopping bucket.
Neither incomplete output establishes equality of complete size-6 streams.

| Executed event | Size 5: finished demand | Size 6: censored demand |
| --- | ---: | ---: |
| Selected eager edges | 13,613,410 | 6,530,878 |
| Ready expansions | 6,938,011 | 3,736,700 |
| Left oracle callbacks | 7,077,884 | 3,780,978 |
| Fast root skips | 3,427,604 | 1,636,736 |
| Left oracle rejections | 138,866 | 44,278 |
| Node-merge empty failures | 6,419,835 | 2,614,276 |
| Class-assimilation empty failures | 34,041 | 1,744 |
| Core representative getter calls | 84,546,460 | 35,529,293 |
| Oracle representative getter calls | 41,812,589 | 42,268,199 |
| Oracle partial-UVar visits | 31,991,574 | 41,475,771 |
| Oracle pending-check representative reads | 9,821,015 | 792,429 |
| All partial-node visits | 54,201,728 | 68,782,526 |

All node-merge empty failures have annotation and constraint roles. An empty
intersection can result from symbols, paths, or recursion. It is not a count
of distinct invalid programs or logical type contradictions. The counters
observe executed guards. They do not scan unchosen alternatives or infer
failures by subtracting callback totals.

Both windows record only one program ready-slot expansion. Ordinary program
children are constructed recursively inside that expansion, before its Left
oracle callback. They do not each receive a ready-slot callback. The oracle
still sees alternative fragments and later annotation or marker expansions.
These counts do not mean that only one program branch was explored.

All partial-UVar visits have annotation or marker roles. Nodes without a
program role account for 69.44% and 68.81% of partial traversal visits.
Class merges can retain several roles. These observations do not identify
which positions a later template wildcard ignores. For size 5, oracle getters
equal partial-UVar visits plus pending-check reads exactly. The interrupted
size-6 count differs by one tick.

These are instrumented event counts, not time, allocation, or RSS shares.
An earlier diagnostic configuration failed output agreement and was
discarded. The accepted configuration retains the normal pruner compiler
options. The counts support a root-only fragment-view experiment. A template
wildcard can then omit child reads. Repeated reads across templates can offset
that saving. Exact pending IDs, finite languages, residuals, and the full
197-law sequence must agree before any speed claim.

### Cost-centre profiles before and after the fragment check

Profiles compare `d2e91fdf` with the executable body of `09caaec3`; the latter
source differs only in one Haddock sentence. Both use 29 HOME modules, the
same `-O2` late-SCC flags, audited profiling dependencies, and 1064 cases.
Both whole size 5, phase 3 runs reproduce all 197 laws and all 40,814 stdout
bytes. The windows sample the first candidate-list demand in phase 3, size 6,
`Int`, after 8,369 examined terms and 223 laws. Both stop before testing any
candidate from that bucket.

| Source and scope | Application ticks | Pruning self | Enumeration self | `matchPartial` self |
| --- | ---: | ---: | ---: | ---: |
| `d2e91fdf`, whole size 5 | 118,138 | 10,578 (8.9539%) | 24,676 (20.8874%) | 7,104 (6.0133%) |
| `09caaec3`, whole size 5 | 96,639 | 11,951 (12.3666%) | 14,719 (15.2309%) | 6,935 (7.1762%) |
| `d2e91fdf`, size 6 window | 54,409 | 25,472 (46.8158%) | 19,716 (36.2367%) | 19,424 (35.7000%) |
| `09caaec3`, size 6 window | 55,784 | 34,997 (62.7366%) | 12,629 (22.6391%) | 23,931 (42.8994%) |

Denominators exclude GC, profiling, system, and idle ticks. The module self
columns are disjoint; `matchPartial` is part of Pruning. Whole runs include
testing and completion. `QuickCheck.Gen` has 22,062 self ticks (22.8293%) in
the new whole run. That fraction does not apply to the later demand window.
The censored windows do not complete equal amounts of work. Their percentages
do not measure native speed or allocation changes.

The new window lasts 60.685 seconds wall and 61.338 seconds CPU under its
60-second guard. Its sampled allocation delta is 256,932,169,784 bytes
(239.287 GiB). The earlier window lasts 61.193 seconds wall and 61.845 seconds
CPU, with a 217.923 GiB sampled delta. Only profile ticks belong to each window;
profile allocation and entry totals still include the preceding search.
All 28,995 new stdout bytes match the closed 300-second native trial, including
223 complete laws. The older 24,576-byte output is also an exact prefix.
Neither observation establishes complete size-6 output agreement.

Matching remains the largest named self cost in the new window. Its total
includes structural and full typed checks. `programs`, `indexTemplates`, and
`fragmentTerm` have 1,031, 1,005, and 356 self ticks. The index serves both
sets of templates. `rejectEarly` and the early-index bindings have no separate
surviving labels. Anonymous `Pruning.go2` has 6,545 self ticks without a source
location. These facts do not assign a cost to an inlined helper.
`prunedTerms` contains 55,514 inclusive ticks (99.5160%). The partial expander
contains 25,872 (46.3789%), including matching continuations. These inclusive
figures overlap and do not measure removable getter cost. Profiler entries
are not independent read counts.

The new whole profile takes 118.929 seconds versus 34.785 seconds native:
3.4189 times as long. The corresponding earlier observation is 142.012
versus 36.248 seconds, or 3.9178 times. These ratios measure instrumentation
distortion on two whole runs. They are not speedups or window corrections.

### Completed pruning controls

Two local candidates preserve the exact current 197-law HugeLists size 5,
phase 3 output. All stdout bytes match the selected `d2e91fdf` reference.
The root-view candidate reads fragments during monadic template matching.
The lazy snapshot candidate keeps the old pure matcher and captures immutable
union-find and value maps.

| Measurement | `d2e91fdf` pruning | Root view | Lazy snapshot |
| --- | ---: | ---: | ---: |
| Allocated bytes | 229,664,980,896 | 253,776,344,696 | 221,111,957,160 |
| Allocation change | reference | +10.4985% | −3.7241% |
| RTS total CPU time, s | 36.237 | 39.201 | 39.718 |
| Observed CPU change | reference | +8.1795% | +9.6062% |
| Wall time, s | 36.248 | 39.233 | 39.708 |
| Peak RSS, KiB | 533,840 | 533,572 | 528,692 |

Each variant runs once. The snapshot comparison reuses the completed baseline.
Both comparisons use the same eleven HOME modules and audited dependencies at
`-O2`, the full 1,064-case schedule, and `-N1 -M6G`. Compiler flags match.
Neither native control uses counters or profiling. Each scope has a 16 GiB
limit and no swap. These observations do not estimate timing noise or
statistical significance. No original Spectacular run is repeated.

Both candidates pass nine finite grammars with 36 template sets each. These
controls compare pending IDs and order, template selection, annotated term
sequences, multiplicities, and residual multisets. The snapshot also preserves
saved trees across later value writes and unions, including implicit singleton
roots and repeated original hole IDs. These checks do not prove equivalence
for every recursive state or establish a residency bound.

The root view increases allocation. The snapshot saves modest allocation but
has higher observed CPU time. Neither fragment-view API is selected. The
comparison matrix retains its `d2e91fdf` measurements.

A whole-run late-SCC profile of the rejected root view also reproduces the
full 197-law stdout. Its 29 HOME modules use `-O2`. Matcher self costs total
15,916 of 108,008 application ticks (14.7359%). The denominator excludes GC,
profiling, system, and idle ticks. Sampling includes testing and completion;
it does not isolate the earlier enumeration bucket.

The fragment-view subtree has 22,687 ticks (21.0049%). It includes all matcher
self costs through enumeration's continuations. It is not removable lookup
cost. Inclusive families overlap. Program discovery, index, spine, and resume
helpers have no separate surviving labels; this does not establish zero cost.
Profiler entries are not independently validated UVar-read counts.

Profile wall time is 132.883 seconds, versus 39.233 seconds for the native
candidate, or 3.387 times as long. Profiling also changes allocation and RSS.
Without a matched baseline profile, these percentages do not attribute the
native regression or predict a speedup from another implementation.

### Compiled template controls

An arity-aware census identifies 163 of the 173 entry templates whose
program patterns do not inspect annotations. Ten still require annotation
checks. The earlier count of 161 confused the `filter` constant with the
program wrapper: their arities are one and two. The two added templates have
no hits in the incomplete 512-run sample. This correction is not a speedup.

A local control applies public `exclude` at program positions for the fixed
pattern `((+) 0) x`. All 197 laws and all stdout bytes match. Allocation is
229,727,802,864 bytes versus 229,664,980,896 bytes in the retained baseline,
an increase of 0.02735%. One run per variant cannot estimate timing noise.
The finite controls pass 32 applied checks and explicitly skip 12. The nested
`+0` case keeps the same 320 annotated/residual records from 640 raw runs.
A separate ambiguity control reduces two surviving runs to one while keeping
the same term set. Generic exclusion therefore does not preserve raw-run
multiplicity. This experiment does not select a production transformation.

The all-163 finite control completes 63 applied groups and skips 27. It then
hits its 90-second guard in a nested case. Total allocation is
240,076,346,056 bytes; maximum residency is 8,363,416 bytes. The unfinished
case has no internal stage markers. Its cost cannot be assigned to exclusion
construction, either enumeration, or the final comparison. The remaining
correctness gate is unknown, and no native run follows it.

A separate actual-entry construction profile preserves the exact 133-law
prefix, then hits its 60-second transform guard. Its 30 HOME modules use
`-O2` and late SCCs. The whole process has 87,062 application ticks, including
the prefix. The `compileTemplates`/`refine` ancestry contains 54,133 ticks
(62.1775%). Within that ancestry, `edgeCopies` has 17,306 self ticks,
or 31.9694% of those construction ticks. These are distinct from the
whole-process denominator. The transform does not finish. This profile
identifies construction work but gives no correctness result or native cost.

A separate private conjunction shortcut in `Template` keeps its public API.
Its finite intersection, split-order, and construction controls pass. The
finite process completes in 0.453 seconds, with 72 applied groups and 27 skips.
The earlier unmodified finite attempt stopped at 90 seconds; these results
do not give a matched completed-work timing ratio. The new 13-module native
build uses `-O2`. Its actual-entry pilot preserves the exact 133-law prefix
but hits the 60-second transform guard. No transformed graph is reported,
and no full 197-law run follows. The whole prefix-plus-transform process uses
69.210 seconds wall, 69.274 seconds CPU, and 306,341,183,760 allocated bytes.
Maximum residency is 92,051,104 bytes and peak RSS is 222,020 KiB. These totals
are not transform-only costs. Finite success does not establish a real-bucket
gain. This CFTA change remains unselected.

Two further controls reproduce all 197 laws and all stdout bytes. One adds
checks during CFTA child construction. The other changes only Specftacular,
using the existing Left callback. Both retain all 173 entry templates and add
163 pure structural checks. These checks omit the fixed arrow marker without
resolving its UVar. The fixed-marker and program/type encoding assumptions
remain explicit. Both arms pass nine finite grammars with 36 template sets.
These controls are not a general raw-language equivalence proof.

| Measurement | Retained baseline | Spec-only callback | CFTA subterm check |
| --- | ---: | ---: | ---: |
| Allocated bytes | 229,664,980,896 | 209,715,175,160 | 207,057,677,992 |
| RTS total CPU time, s | 36.237 | 34.794 | 34.117 |
| Peak RSS, KiB | 533,840 | 530,820 | 537,888 |

The Spec-only arm reduces allocation by 8.6865%. The CFTA arm saves a further
1.2672%, with 1.9457% lower observed CPU time and 1.3315% higher RSS. Each arm
runs once against the same retained baseline; timing noise is not estimated.
The CFTA extension is not selected for this small additional saving.

The committed Spec-only guard also passes fresh native and GHC checks. Its
seven core HOME modules and the GHC adapter compile at `-O2` against the
retained audited libraries. Existing checked and unchecked goldens pass.
All three frontends retain the exact 24-law Lists and 9-law Monad sequences.
Fresh carrier and function-generator alias probes pass. The Lists size 4,
phase 1 control keeps all ten laws. It allocates 201,181,832 bytes and uses
507,230,261 Cachegrind instructions, decreases of 0.2123% and 0.1188% against
the retained `d2e91fdf` counters. The new core is a HOME build; the retained
small control used packaged modules. This build-context difference remains
explicit. No baseline is rerun. CFTA sources and archives remain unchanged.

The Spec-only arm still times out on size 6, phase 3 after 300.157 seconds
wall and 300.529 seconds CPU. The actual phase 3, size 6, `Int` bucket starts
after 52.537 CPU seconds, with 8,369 examined terms and 223 laws. It remains
unfinished after another 247.615 seconds wall and 247.955 seconds CPU.
Whole-process allocation is 1,885,469,660,616 bytes, maximum residency is
203,768,576 bytes, and peak RSS is 613,936 KiB. These phase-only events do not
identify demand, testing, or completion costs within the bucket.

All 223 printed laws are complete lines. The earlier 24,576-byte native
output is an exact prefix, including its unfinished equation 171. This does
not establish complete size-6 output agreement. There is no matched timing
ratio against the older 900-second trial. No baseline or original run is
repeated. The Spec-only change is committed as `09caaec3`. The full matrix continues
to report the measured `d2e91fdf` reference.

### Alternatives supported by these diagnostics

1. **Share type witnesses for each program shape.** Join fresh constant type
   schemes with rigid generated-variable types before creating annotation
   branches. Retain the exact relation between each program and its annotated
   runs. Preserve concrete types, residual obligations, recursion boundaries,
   and raw multiplicities. A single principal instance cannot replace that
   relation. KBO compares annotations before later arguments. Each witness
   family therefore needs a certified minimum and a resumable remainder.
   The 512-run sample shows no duplicate complete witnesses. The demand
   counters instead locate millions of empty annotation merges. A witness
   join must remove enough of that work to justify the larger change.

2. **Compile shared template exclusion before creating branches.** Use
   `excludeAnywhere` as the exact-language reference. Its open patterns can
   create exponential subset products. Build only reachable products for a
   shared recognizer, with a state budget before global interning. Fall back
   to the existing oracle at that limit. Retain typed template eligibility,
   edge constraints and residual obligations. Generic exclusion can merge
   ambiguous surviving runs. Exact raw multiplicity needs a separate argument;
   term-language equality alone is insufficient. A repeated `Hole` is not a
   named equality binder. Measure compilation plus
   enumeration on the actual bucket-entry templates. Keep the final KBO sort
   for this experiment. Faster matching alone does not remove type branches.

3. **Certify minima for annotations and remaining siblings.** Unresolved
   annotation bounds remain below complete annotations. Sibling sources also
   retain one conservative ancestor bound. First identify which bound keeps
   each failed frontier entry early in the queue. Then use grammar sharing
   to improve its certificate without sorting all complete siblings. Retain
   `Unknown` when correlations prevent a tighter bound. Prove each bound
   against canonical KBO, including annotation order. Raw node counts alone
   are insufficient. Keep the same frontier cap and require complete-stream
   agreement, ordered keys, and correct pause/resume behavior.

These proposals preserve phase and type traversal, program-leaf size order,
occurrence generalization, and the parametricity contract. They are not
measured improvements. Stronger pruning requires valid equations under the
selected comparator. A finite test schedule does not establish that
validity.

## Memory and allocation

QuickSpec 2's sparse [decision tree][qs-tree] retains counterexamples that
separate representatives. The current engine follows that design. A leaf
retains a term evaluator. A branch retains one discriminator case and its
values. Test cases store seeds and boundary indexes. Each comparison
generates only the variables used by either term. Both evaluators use the
same valuation for that case. The tree retains a valuation only through
discriminator values. It does not retain all generated nested lists and
complete result vectors at every representative.

A local control before the completion changes restores shared input maps and
retained result vectors. It also restores the legacy decision tree's prefix
comparisons. It keeps the same pruning, proof shortcut, and available
validation cases. The strategies compare cases in different orders. They can
therefore treat partial values differently. This control compares evaluation
strategies, including storage. It does not isolate storage alone. All
variants produce the same 29 numbered Lists5P4 laws.

| Lists5P4 storage control before completion changes, 1000 + 40 cases | Peak RSS, MiB | Allocated, GiB |
| --- | ---: | ---: |
| Shared inputs and retained result vectors | 1920.5 | 20.93 |
| Sparse evaluation | 51.4 | 20.59 |
| Sparse evaluation with native runtime checks | 54.2 | 21.36 |

Current selected-runtime memory controls:

| Control | Native unchecked MiB | Native checked MiB | GHC MiB |
| --- | ---: | ---: | ---: |
| Lists5P4 | 49.7 | 55.7 | 533.0 |
| ListMonad6P4 | 87.2 | 92.8 | 546.0 |

The fresh selected native unchecked, native checked, and GHC controls retain
the exact 24-law Lists and nine-law Monad sequences. The GHC process
includes the compiler and interpreter. These smaller bases differ from the
historical 29-law storage control. Agreement does not prove coverage
equivalence. Across independently measured processes in both passes, peak
RSS is 1078.4 MiB (HugeLists-5-p4, 900-second limit). The largest reported
RTS allocation is 547.324 GiB (HugeLists-7-p2, 300-second limit). Missing
timeout RTS totals remain unknown. Allocation is cumulative traffic, not
simultaneous memory use.

Sparse evaluation regenerates inputs to reduce retained memory. In the
storage control, it uses 97.3% less peak RSS and allocates 1.6% less.
Retaining the complete input maps and result vectors restores the large
peak. These controls do not establish an isolated automaton speed
improvement.

On Lists4P1, Cachegrind records 1,426,503,315 instructions for retained
vectors and 445,870,706 for sparse evaluation. RTS allocation is 521,257,520
and 178,430,168 bytes respectively. These controls vary the evaluation
strategy in the same source revision. They precede the completion changes
measured above.

## GHC frontend

`specftacular-ghc` shares the type checks, rewrite rules, validation
schedule, partial-term oracle, and sparse evaluator. It assigns distinct
carriers to unconstrained type variables in binder order. Variables that
occur in constraints remain concrete. Container class variables use lists.
Other constrained variables use `Int`. An independent `HasCallStack`
predicate does not prevent an unrelated variable from remaining abstract.

GHC resolves generators for required types. These include functions whose
custom domains have `CoArbitrary` instances declared in the session. A
signature function can have at most five unconstrained type variables.
Generated source still needs unambiguous constructor names in the session.
These probes do not cover qualified-only imports or constructor-name
collisions. Focused probes cover distinct carriers, ordinary and nested
class constraints, `HasCallStack`, custom function generation, and `usort`.
The native and GHC `usort` probes both remove duplicates.

The session compiles carrier payloads at `Int`. Its resolver can reuse a
generator or equality for a new logical type only when both types have the
same physical type tree. It updates logical names and prefixes. Fresh `[B]`
and `C -> D` generator probes pass. The 1064-case control also checks a
fresh `B -> Bool` predicate and `[B]` list through GHC
filter/takeWhile/drop, and both half-range overflow witnesses through GHC
drop and Int addition. Each returns a false equality with the resolved
logical `[B]` comparator. This fallback does not add runtime type checks.

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
requests one test and pruning size 9. ListMonad limits test size to 20. The
benchmark programs use separate settings.

QuickSpec 2's [`arith`][qs-arith] supplies `0`, `1`, and `(+)` as background
functions. Its [driver][qs-driver] first explores them. It retains their
laws for pruning and suppresses output about only background functions.
These are discovered laws, not a fixed list of arithmetic axioms. Section
3.6 of the [QuickSpec 2 paper][qs-paper] explains the procedure.

Spectacular's and Specftacular's adapted `arith` supply only `0` and `1`. A
missing equation with `(+)` does not establish a discovery regression in
that workload. The fork's benchmark counts `length res` from
`quickSpecResult`. Its driver includes hidden background laws in that
result. Thus 25 printed Lists laws versus the paper's 28 benchmark laws can
be an accounting difference. The saved file does not verify the hidden-law
count. Compare foreground functions, background functions, generators, test
settings, and count policy before attributing such differences to the
engine.

# Amendments

These corrections distinguish problems in the published artifact and paper
from regressions in the port. The current implementation fixes the code
problems described below. It does not change the published artifact or
retroactively repair the historical cross-tool comparison.

1. **The example includes an invalid general law.** Figure 7, law 9, gives
   `f x == f (f (f x))`. Integer successor is a counterexample. The published
   Boolean carriers explain the identity. Integer-carrier controls reject
   that identity in the recorded workloads.

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
completion consequences. The output is not proved minimal or complete. The
new inputs reject all six counterexamples in actual-name replay. Fresh
output omits all six equations. The six-target and broad coverage checks
above state their exact scope. Neither more completed configurations nor
finite tests prove all printed laws. Predicate indexes with the same residue
modulo eight remain outside the new pairwise guarantee. Unsupported types
retain generator-based testing.

Validated generalization supports at most five independent type binders and
keeps the original result type and equality function. Missing generators or
failed validation retain the original equation. The checks depend on
parametric signature constants. They neither prove a free theorem nor test
every type. A finite test can still admit a false scheme that affects
subsequent pruning. The reduction replay also reaches its existing 100-pass
limit without a fixed point; the worklist does not remove that budget.

A partial representative can block later candidates after an equality
exception. The sparse evaluator does not fix partial-term discovery. Further
work can study QuickSpec 2's observational results and totality checks
without changing custom non-strict equality behavior.

Regex equality compares acceptance on 100 fixed words, with seed 12345 and
size 10. The current benchmark prints that policy. It remains sampled
observation, not exact regular-language equivalence.

The artifact rerun does not explain every historical law count. For example,
the original size-7 phase-2 HugeLists run with a 120-second limit gives 181
laws, while Table I gives 186. Different saved examples and benchmark
settings must not be treated as the same experiment.

Strict GHC builds pass for both packages and their benchmark executables.
Existing golden tests pass in both native modes. Fourmolu and cabal-gild
checks apply. Focused inference controls and native checked/unchecked
proposal probes check independent carriers, missing instances, false laws,
the actual equality policy, and cancellation. Raw measurements, CSVs, source
checkouts, and local task notes remain outside this package. This report
contains the results and the source references needed to interpret them.

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

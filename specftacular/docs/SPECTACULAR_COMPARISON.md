# Spectacular and Specftacular

The matrix compares original Spectacular with Specftacular `8c44a0d9b`. On
one core, this revision completes 25 of 27 configurations within 900
seconds. On 12 cores (`-N12 -qn4`, `--parallel-tests 64 --speculate 64`),
it completes all 27, HugeLists 7-p3 and 7-p4 with
`--type-depth 2 --recheck 2000`. The completion of a law stops after 2^15
critical pairs (see [Completion fuel](#completion-fuel)), and on 12 cores
the completions and the comparisons use the other capabilities (see
[Parallel completion and tests](#parallel-completion-and-tests)), so
HugeLists 7-p4 completes in 57 minutes. Phase 4 enumerates programs
without their type annotations (see [Phase 4 programs](#phase-4-programs)),
so HugeLists 6-p4 with the defaults completes in both modes. Original reference measurements remain unchanged.
Sections that name an earlier revision describe that revision.

The runtime compiles eligible rewrite templates into supported size/type
graphs, applies one reduction pass, and retains the remaining partial-term
oracle. It preserves increasing program size, occurrence generalization,
validated polymorphic schemes and canonical annotated KBO within each bucket.
It uses the existing enumerator and final bucket sort. Pruning precedes value
testing. The input schedule contains 1064 cases.

The [current profile](#current-whole-run-profile) measures the
selected template and helper implementation. Earlier profiles retain their
revision labels. A larger law count is not a better result by itself. False
and redundant equations increase the count.

## Sources and method

The original columns retain the earlier all-`-O2` measurements. Original
Spectacular and QuickSpec 2 are not rerun. The new matrix measures
`cf1bee8f` with the 1064-case schedule. HugeLists size 5, phase 3 and size 7,
phase 2 adopt the two completed candidate controls. These controls compile
30 HOME modules at `-O2` and contain the exact selected runtime sources.
Other measured coordinates use fresh packaged executables. Same-size
timeout inference can avoid a redundant later-phase process. No b530 timing
row is reused as a current measurement.

The adopted controls used internal guards of 300 and 900 seconds. Both
completed within 300 seconds. They are adopted completions, not new
300-second processes. The HOME/package distinction remains explicit.

| Input | Revision |
| --- | --- |
| [Published Spectacular artifact](https://zenodo.org/records/7565003) | `00621f4f0f03e5d0afea3c730434a8842e473546` |
| [Preceding child-part identifier change](https://github.com/TharkunAB/cfta/commit/f4ec36bd7b05c3478c92fbcb7e2e763bdad39e6b) | `f4ec36bd` |
| Parallel completion and tests matrix (`improve/parallel-completion-tests`) | `8c44a0d9b` |
| Completion fuel matrix (`improve/completion-fuel`) | `b07337367` |
| Phase 4 programs matrix (`improve/phase4-programs`) | `2b2d9e562` |
| [Preceding matrix](https://github.com/TharkunAB/cfta/tree/13424d8f9fbed3e564dd39793eef5a86e94e09c9/specftacular) | `13424d8f9` |
| [Current bounds and Sequence matrix](https://github.com/TharkunAB/cfta/tree/cf1bee8f4017a6cd04a36d35bda31d1a6d40e78f/specftacular) | `cf1bee8f` |
| [Preceding carried-identifier matrix and one-hour trials](https://github.com/TharkunAB/cfta/tree/b530f920586b6551a4c2bdead16a58ca46e7196c/specftacular) | `b530f920` |
| [Preceding f4ec matrix and profile](https://github.com/TharkunAB/cfta/tree/f4ec36bd7b05c3478c92fbcb7e2e763bdad39e6b/specftacular) | `f4ec36bd` |
| [Preceding all-bucket matrix and profile](https://github.com/TharkunAB/cfta/tree/d898645376ae5f1e9b8e5c7b5e0b7dcfa5bfd9e8/specftacular) | `d8986453` |
| [Historical 1064-case matrix and typed coverage](https://github.com/TharkunAB/cfta/tree/d2e91fdf297659382329e8d9375082024439dc8c/specftacular) | `d2e91fdf` |
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
covers 53 external units.

The cf1bee8f packaged build has fresh effective `-O2` commands for 7/7
native/GHC local components and 100/111 external entries. Entries include
build tools; compiler-distributed libraries retain their toolchain settings.
Native unchecked, native checked and GHC sequences agree: 24 laws for Lists
size 5, phase 4 and 9 for Monad size 6, phase 4. Physical alias controls
pass.

The existing checked and unchecked goldens pass.

Builds and runs use `nix-shell`, `heavy-management`, and pueue. Packaged
matrix and frontend jobs use a verified 16 GiB cgroup cap and no job swap.
The adopted HOME controls, whole-run profile and library budget use an
8 GiB cap. HOME benchmark and profile runs use `+RTS -N1 -M6G -s -RTS`. These runs
accepted concurrent load. Packaged benchmarks use the same RTS limits and
a low-load preflight, which does not reserve the host. These limits remain
below the requested 80 GB maximum. Machine activity can change during a
run, so elapsed-time ratios do not isolate engine speed.

The matrix covers the 27 Table I configurations. Original runs have a
60-second limit. The Specftacular runs of `8c44a0d9b` have a
900-second limit on one core, and no limit that a run reaches on 12 cores
(see Results). The paper used 3600 seconds. These
different limits must remain explicit. A same-size later phase can be
inferred after an earlier-phase timeout at the same limit. Such an entry
has no independent cost or law-count measurement. No inference crosses
maximum sizes.

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

### Published Table I and the current revision

[Table I in the extended paper](https://mpg.is/papers/gissurarson2023spectacular-extended.pdf#page=8)
reports 23 of 27 Spectacular configurations completed within 3600 seconds.
Its four timeouts are HugeLists5P4, HugeLists6P4, HugeLists7P3 and HugeLists7P4.
The main table instead retains our original artifact runs at 60 seconds:
20 completions and seven timeouts. These are separate measurements.

The selected cf1bee8f matrix completes 24 configurations within 300 seconds
and 24 within the 900-second policy, including retained completions. All 23
configurations completed in the paper also complete in the new 300-second
pass. Additional completed configurations against the paper: HugeLists-5-p4.

| Configuration | Paper seconds | Paper memory, as printed | Paper laws | cf1bee8f seconds (300 s pass) | New peak RSS MiB | New laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists7P4 | 105.25 | 155.34 MB | 93 | 23.86 | 225.5 | 41 |
| Regex7P2 | 10.64 | 16.9 MB | 42 | 50.39 | 48.3 | 60 |
| HugeLists5P3 | 83.7 | 106.9 MB | 144 | 21.37 | 547.0 | 197 |
| HugeLists5P4 | >3600 | 301.3 MB | — | 145.98 | 1246.9 | 305 |
| HugeLists6P3 | 3164.75 | 434.4 MB | 211 | 124.38 | 1106.4 | 330 |
| HugeLists7P2 | 201.51 | 54.6 (unit omitted) | 186 | 93.31 | 923.3 | 242 |

The two HugeLists5P3/7P2 rows adopt completed candidate HOME controls.
Other measured rows use fresh packaged binaries. The paper used a 32 GB
cloud machine with six 2 GHz Xeon vCPUs. Paper memory retains its printed
units. Hardware, compilers, generators, validation, usort semantics
and equation correctness differ. These are completion/resource comparisons,
not matched speed ratios. Law counts do not establish validity or independence.

## Results

The original `T` means a 60-second timeout. A timeout has no final law
count. HugeLists uses different `usort` definitions in the two
implementations, so its outputs are not identical workloads.

The Specftacular columns measure revision `8c44a0d9b` of
`improve/parallel-completion-tests`, built at `-O2` with GHC 9.14.1. The
binaries came from an earlier commit with the same code and other
comments. The completion of each law takes at most 2^15 critical pairs,
the default (see [Completion fuel](#completion-fuel)). The runs ran one at
a time through pueue in one 56 GiB cgroup on 2026-10-25 (CET): the
one-core runs from 06:09 to 07:33, and the runs on 12 cores from 07:33 to
08:58. No other job ran. The load average at the start of a run was 1.2 to
3.5, and 1.3 to 5.3 on 12 cores, most of it from the run before. Except
where `ᵈ` marks it, no run in this table uses `--recheck`, so a printed law
can be false.

- One core: the defaults, `+RTS -N1 -M14G`, and a 900-second limit. `T`
  is a timeout. A timeout skips the later phases of the same size
  (`T (inferred)`).
- 12 cores: `+RTS -N12 -qn4 -A64m -M52G`,
  `--parallel-tests 64 --speculate 64`, without `--enumerate-ahead`, and
  no time limit that a run reaches. Each phase enumerates the parts of a
  bucket in parallel, a comparison tests its cases after the first 64 in
  parallel, the completion of a law decides its critical pairs in
  parallel, and four threads collect the garbage. The peak RSS includes the
  twelve 64 MiB allocation areas. `ᵈ` marks a run with
  `--type-depth 2 --recheck 2000`: without the depth bound, phase 3 at
  size 7 does not finish, and without the recheck a false law stops the
  search (see below).

| Signature | Size | Through phase | Original s (60 s limit) | Original MiB | Original laws | One core s (900 s limit) | One core MiB | One core laws | 12 cores s | 12 cores MiB | 12 cores laws |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists | 7 | 2 | 1.07 | 21.6 | 32 | 0.45 | 43.9 | 15 | 0.57 | 817.9 | 15 |
| Lists | 7 | 3 | 18.11 | 70.8 | 73 | 10.63 | 1563.7 | 33 | 5.96 | 2379.0 | 33 |
| Lists | 7 | 4 | T | 139.5 | — | 23.90 | 1565.3 | 41 | 11.47 | 2381.4 | 41 |
| Octonions | 7 | 2 | 0.15 | 21.4 | 8 | 1.00 | 29.1 | 15 | 0.46 | 808.0 | 15 |
| Octonions | 7 | 3 | 0.17 | 20.1 | 8 | 0.94 | 29.4 | 15 | 0.49 | 802.4 | 15 |
| Octonions | 7 | 4 | 0.22 | 24.3 | 8 | 1.00 | 29.1 | 15 | 0.48 | 804.5 | 15 |
| Regex | 7 | 2 | 3.06 | 18.7 | 42 | 51.09 | 57.2 | 60 | 33.20 | 847.7 | 60 |
| Regex | 7 | 3 | 4.29 | 16.8 | 42 | 50.76 | 59.3 | 60 | 32.95 | 842.0 | 60 |
| Regex | 7 | 4 | 5.84 | 17.1 | 42 | 51.68 | 67.8 | 60 | 34.12 | 844.8 | 60 |
| ListMonad | 7 | 2 | 0.27 | 15.4 | 8 | 4.42 | 57.9 | 9 | 2.65 | 818.7 | 9 |
| ListMonad | 7 | 3 | 0.46 | 22.3 | 8 | 4.55 | 59.9 | 9 | 2.92 | 822.0 | 9 |
| ListMonad | 7 | 4 | 18.04 | 208.8 | 42 | 4.61 | 65.2 | 9 | 3.43 | 833.9 | 9 |
| HugeLists | 3 | 2 | 0.07 | 12.1 | 22 | 0.19 | 56.0 | 28 | 0.31 | 565.0 | 28 |
| HugeLists | 3 | 3 | 0.18 | 17.0 | 27 | 0.33 | 56.7 | 40 | 0.49 | 800.4 | 40 |
| HugeLists | 3 | 4 | 0.64 | 30.7 | 33 | 2.54 | 660.0 | 46 | 1.43 | 1074.7 | 46 |
| HugeLists | 4 | 2 | 0.20 | 14.3 | 37 | 0.79 | 74.6 | 46 | 0.90 | 827.2 | 46 |
| HugeLists | 4 | 3 | 1.37 | 36.3 | 68 | 2.50 | 159.7 | 84 | 2.22 | 907.6 | 84 |
| HugeLists | 4 | 4 | 28.43 | 122.7 | 90 | 8.58 | 1010.8 | 122 | 5.87 | 1489.4 | 122 |
| HugeLists | 5 | 2 | 0.88 | 23.2 | 66 | 7.96 | 220.5 | 92 | 7.31 | 989.6 | 92 |
| HugeLists | 5 | 3 | 27.27 | 104.8 | 144 | 23.69 | 1442.7 | 197 | 19.16 | 1632.5 | 197 |
| HugeLists | 5 | 4 | T | 165.1 | — | 55.90 | 2196.1 | 291 | 42.10 | 2724.7 | 291 |
| HugeLists | 6 | 2 | 6.37 | 39.1 | 99 | 12.09 | 298.6 | 130 | 10.84 | 1020.2 | 130 |
| HugeLists | 6 | 3 | T | 305.6 | — | 102.72 | 1847.3 | 330 | 93.23 | 2730.3 | 330 |
| HugeLists | 6 | 4 | T | 308.9 | — | 491.05 | 6683.7 | 690 | 364.06 | 14669.5 | 690 |
| HugeLists | 7 | 2 | T | 60.2 | — | 79.54 | 983.3 | 242 | 76.38 | 1645.4 | 242 |
| HugeLists | 7 | 3 | T | 58.0 | — | T | 2931.4 | — | 916.93 ᵈ | 7763.7 | 691 |
| HugeLists | 7 | 4 | T | 55.6 | — | T (inferred) | — | — | 3392.93 ᵈ | 30667.0 | 1413 |

On one core, 25 of the 27 configurations complete within 900 seconds.
HugeLists 7-p3 times out in phase 3, with 381 laws printed, and 7-p4 is
inferred. On 12 cores, all 27 configurations complete. Each configuration
gives the same output as at `b07337367`, byte for byte, on one core and on
12 cores, where `b07337367` ran without `--parallel-tests` and
`--speculate`. At `b07337367`, the outputs were the same as at
`2b2d9e562`, except HugeLists 7-p3 and 7-p4 on 12 cores, where completions
run out of their fuel (see [Completion fuel](#completion-fuel)).

HugeLists 6-p4 with the defaults completes in both modes, with 690 laws:
in 491 seconds on one core, with a maximum residency of 2.3 GB, and in 364
seconds on 12 cores, with a maximum residency of 5.0 GB. At `b07337367`,
it took 486 and 477 seconds. At `2b2d9e562`, without the fuel, it took 577
seconds on one core and 595 seconds with `--enumerate-ahead`. At `13424d8f9`, it timed out at 900
seconds on one core, a longer one-core run exhausted a 14 GiB heap after
1,668 seconds, and with `--enumerate-ahead` the RSS reached 47.8 GiB after
2,601 seconds, at the cap of the cgroup. The memory grew in the completion
of a series of laws of this form:
`length (zip (zip xs ys) zs) == length (zip (zip xs zs) ys)`.

Without `--recheck`, HugeLists 7-p3 and 7-p4 with `--type-depth 2` accept
law 402 of phase 3,
`drop (length (concat xs)) xs == reverse (drop (length (concat xs)) xs)`.
The law is false when `xs` contains empty lists, but it holds on the 1064
test cases. Its rewriting prunes most of the rest of the search: phases 1
to 3 examine 41,070 terms against 178,455 with the recheck, and phase 4
examines 65 terms and finds no law. 7-p3 then completes in 1,345 seconds
with 444 laws, and 7-p4 in 2,377 seconds with the same 444 laws. With
`--recheck 2000`, the recheck drops the law, so the two cells use it.

HugeLists 7-p4 on 12 cores completes in 3,393 seconds (57 minutes). At
`b07337367`, it took 4,256 seconds under a load of 1.7 to 6.9. At
`2b2d9e562`, with `--enumerate-ahead` and without the fuel, it took 14,081
seconds, and 24,715 seconds at `13424d8f9`. It allocates 24.6 TB against
22.7 TB at `b07337367` and 61 TB at `2b2d9e562`, and its CPU time is 16,191
seconds against 13,233 and 35,088 seconds. Its maximum residency is
12.0 GB, against 12.4 GB at `b07337367`, 19.5 GB at `2b2d9e562` and 7.3 GB
at `13424d8f9`, and its peak RSS is 29.9 GiB. The cause of the larger
residency is not known yet. It finds 1,413 laws against 1,946 at
`2b2d9e562` ([Completion fuel](#completion-fuel) gives the difference), and
the recheck drops 166 laws against 249. Five completions keep only the
rules of their laws, over the allocation budget, against three at
`b07337367` (see [Parallel completion and tests](#parallel-completion-and-tests)).

At `b07337367`, other flags gave the same 1,413 laws. With
`--enumerate-ahead`, background threads enumerate the parts of the next
types of a size, and the parts stay until the size ends, so the live heap
is larger and the collections take more time. Two runs with
`--enumerate-ahead -qg` took 6,381 and 6,089 seconds. All runs use `-N12 -M44G` and `--type-depth 2 --recheck 2000`. The
load was 1.7 to 6.9 during them, so the seconds are upper bounds.

| Flags | Seconds | GC seconds (elapsed) | Maximum residency GB | Peak RSS GiB | Over the memory limit |
| --- | ---: | ---: | ---: | ---: | ---: |
| `--enumerate-ahead`, `-qg -A64m` | 6,381 | 2,765 | 18.4 | 38.3 | 3 |
| `--enumerate-ahead`, `-qn4 -F3 -A64m` | 5,049 | 1,388 | 15.8 | 45.4 | 3 |
| `-qg -A64m` | 5,159 | 1,293 | 11.8 | 28.9 | 0 |
| `-qn4 -A64m` | 4,256 | 372 | 12.4 | 30.7 | 0 |

Without `--enumerate-ahead`, the completions of the three laws over the
memory limit run out of their fuel instead, so the background threads
trigger the limit.

The law counts differ from those of earlier revisions in some
configurations, for example HugeLists 4-p4 (122 against 125 at
`cf1bee8f`) and 5-p4 (291 against 305). With `--type-depth 2`, the law
counts of HugeLists 7-p3 and 7-p4 are not comparable with the unbounded
configurations.

The original completes 20 runs and times out in seven at 60 seconds.
Different limits do not establish a matched-budget advantage. Single runs
do not estimate timing variance. Allocation is cumulative traffic; it is
not RSS. The Specftacular columns below come from the one-core runs.

| Signature, size, phase | Original allocation GiB | Specftacular allocation GiB | Original residency MiB | Specftacular residency MiB | Original GC CPU s | Specftacular GC CPU s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lists-7-p2 | 4.275 | 1.789 | 5.35 | 10.52 | 0.231 | 0.055 |
| Octonions-7-p2 | 0.419 | 1.611 | 12.58 | 5.01 | 0.026 | 0.032 |
| Regex-7-p2 | 17.185 | 348.338 | 4.47 | 15.01 | 0.474 | 1.710 |
| ListMonad-7-p2 | 0.961 | 26.430 | 3.47 | 16.31 | 0.030 | 1.174 |
| ListMonad-7-p4 | 52.501 | 27.686 | 72.02 | 21.17 | 7.004 | 1.179 |
| HugeLists-4-p4 | 126.783 | 21.409 | 39.68 | 398.82 | 8.920 | 2.425 |
| HugeLists-6-p2 | 24.723 | 50.148 | 17.60 | 106.90 | 1.246 | 1.796 |

### Completion fuel

The completion of a law takes the critical pairs of its rules from a queue.
Since `b07337367`, it takes at most 2^15 = 32,768 pairs
(`--completion-fuel 15`; `0` is no limit). When the fuel runs out, the law
keeps the rules that its completion has derived. These rules follow from
the laws, so the pruning stays sound, but they can prove fewer laws than
the complete rules. The allocation budget of 256 GiB stays as a second
limit. Before the fuel, a completion over the budget kept only the rules
of its law. At HugeLists 7-p4 at `2b2d9e562`, 78 completions did so. They
took 5,738 of the 7,559 seconds of the completion, and their work was
lost. [ADR 7](../../docs/adr/0007-completion-fuel.md) has the decision.

A pair costs about 1 MiB of allocation at HugeLists (0.4 to 2.2 MiB at
6-p4), so the fuel stops a completion at about 32 GiB. A count of pairs
does not depend on the allocation, so the fuel gives the same laws with
each optimization and each number of capabilities.

The fuel changes no output of the one-core configurations and of the
bounded 6-p4 runs, although some of their completions run out of it (three
at 6-p4 with the defaults). On 12 cores, it changes HugeLists
7-p3 and 7-p4. At 7-p3, it adds 11 laws to the 680 of `2b2d9e562` and
removes none. At 7-p4, the outputs agree up to law 344. 578 laws of
`2b2d9e562` are not printed. They are consequences that the rewriting
proves now. At `2b2d9e562`, the completion of
`xs >>= f == concat (map f xs)` ran over the budget, so the law kept only
its own rules, and these consequences were printed as new laws, for
example:

```haskell
concat xss == xss >>= (++) []
[] == xss >>= take 0
xss >>= map f == map f (concat xss)
```

45 laws are printed only with the fuel. They are true consequences that a
stopped completion does not derive, for example:

```haskell
[] == drop x (usort (take x xs))
xs ++ (xs ++ ys) == concat (scanl (++) xs [ys])
concat (drop x [f y]) == (drop x >=> f) [y]
```

Twee 2.7.1 checks the two sets, with 180 seconds for each goal. It proves
147 of the 578 laws from the 1,413 laws with the fuel, and 31 of the 45 laws
from the 1,946 laws of `2b2d9e562`. The first pass gives twee all the laws
of the other run as axioms. The second pass, for the open goals, gives the
axioms that SInE selects at depth 1 and the axioms over the constants of
the goal. Twee shows none of the laws independent. The others stay open
within the time limit.

At 7-p4 on 12 cores, 39 completions run out of their fuel, against 41 at
`b07337367`. Three laws over `[[[A]]]` still run over the allocation budget
within the fuel: their pairs cost more than 8 MiB each. With `--speculate`,
two laws over `[[A]]` and `[[B]]` also run over the budget (see
[Parallel completion and tests](#parallel-completion-and-tests)).

### Parallel completion and tests

At `b07337367`, the tests and the completions ran on the thread that
tests. They took 1,610 of the 4,256 seconds of HugeLists 7-p4 on 12 cores,
while the other capabilities waited. Two flags give them the other
capabilities. Neither changes a decision of the search.

- `--speculate N`: the completion of a law decides up to N critical pairs
  of its queue in threads, under the rules of the moment, and takes the
  decisions in order. A new equation changes the rules, so the pairs after
  it go back to the queue. A decision depends only on the pair and the
  rules, so the decisions are the same. The number of pairs in parallel
  starts at 1 and doubles, up to N, after a step without a new equation.
  After a new equation at position k, it becomes k + 1. At 1, the completion
  decides the next pair on its own thread, with the cache of normal forms.
- `--parallel-tests N`: a comparison at a leaf of a decision tree tests its
  first N cases in order, and the others in one chunk for each capability.
  The first chunk in order that does not agree decides. A chunk stops when
  a chunk before it has found a difference.

[ADR 8](../../docs/adr/0008-speculative-completion.md) has the decision for
`--speculate`.

These runs measure HugeLists 7-p4 (`--type-depth 2 --recheck 2000`) with
`+RTS -N12 -qn4 -A64m` on 2026-10-25, one at a time, with the same 1,413
laws in each row except the last.

| Code and flags | Seconds | Completion seconds | GC seconds (elapsed) | Allocation TB | Peak RSS GiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| `dad3b411b`: `b07337367` with the parts of phases 1 to 3 in parallel | 3,996 | 1,038 | 371 | 22.8 | 29.6 |
| `--speculate 64`, a fixed window of 64 pairs | 4,659 | 1,724 | 434 | 44.2 | 30.6 |
| `--speculate 64` | 3,583 | 633 | 389 | 24.2 | 30.7 |
| `--parallel-tests 64 --speculate 64` | 3,378 | 632 | 495 | 24.6 | 30.0 |
| `--parallel-tests 64 --speculate 64`, the pairs best first | 3,789 | 837 | 364 | 21.8 | 25.8 |

The completion seconds add up the completions that allocate more than
1 GiB. With a fixed window, a new equation came every few pairs in the
large completions, and it discarded most of each batch. The adaptive
window makes the completion 39 % faster. The decisions that it discards
cost 6 % more allocation. The threads have no cache of normal forms, so a
completion counts more allocation against its budget: two more laws run
over it, and keep only their own rules. At this revision, the output does
not change, but a completion near the budget can give other laws.

The parallel tests save 205 more seconds, and the collections take 106 of
them back. At HugeLists 6-p4, they raise the peak RSS from 5.5 to 14.3 GiB
and the maximum residency from 2.3 to 5.0 GB, because twelve comparisons
hold their values and their inputs at once. At 7-p4, phase 4 sets the
peak, so the peak RSS does not grow.

The last row takes the critical pairs in the order of the score of Twee
(2 for each step from the law, the leaves of both sides, and 3 for each
leaf of the larger side), not in the order that they come. At 6-p4, it
gives the same 690 laws in the same order. At 7-p4, within the fuel, it
leaves weaker rules: 52 completions run out of their fuel, and the run
prints 1,826 laws. 458 of them are not in the output of the FIFO order, and
45 laws of that output are not in it. So the queue stays FIFO. `+RTS -N16` on the 24 logical CPUs of the host (12 cores
with two threads each) took 373 seconds at 6-p4, against 368 with `-N12`.

### Phase 4 programs

`2b2d9e562` changes two parts of the search. At the configurations below,
the laws do not change; the time and the allocation do.

- `refine` of cfta, the walk of a template exclusion, keeps a table for
  each exclusion. The table maps a node and the template parts that its
  terms must and must not match to the result. Before, an exclusion
  refined a shared child again for each edge that reached it.
- Phase 4 enumerates the programs of the skeletons without their type
  annotations (see [Enumeration, pruning and typed completion](#enumeration-pruning-and-typed-completion)).
  Before, most choices of phase 4 were the expansions of the annotations:
  60.9 million at HugeLists 6-p4 with `--type-depth 2`, size 6, against
  0.3 million now.

The output of HugeLists 5-p4 (with the defaults and with `--type-depth 2`)
and of 6-p4 with `--type-depth 2` is byte identical to `13424d8f9`. So is
the output of 5-p4 with `--type-depth 2` and `--parallel` or
`--enumerate-ahead` on four cores, against `13424d8f9` with the same
flags, and the output of Lists, ListMonad, Octonions and Regex 7-p4 and
HugeLists 4-p4 and 5-p4. The eight cfta benchmark cells keep their
checksums, and their instruction counts change by less than 0.01 %. The
cfta unit tests and the golden tests pass.

These runs measure HugeLists 6-p4 with `--type-depth 2` on one core
(`+RTS -N1 -M14G`), without diagnostics, with the two revisions of each
row in alternate runs. The load average was 1.2 to 7.1.

| Revisions | Allocation GB | MUT seconds, two runs each |
| --- | ---: | ---: |
| `13424d8f9` | 2,211 | 376.3, 361.4 |
| `13424d8f9` and the `refine` table | 1,800 | 297.3, 314.0 |
| `13424d8f9` | 2,211 | 412.3, 404.7 |
| `2b2d9e562` | 1,382 | 265.4, 250.9 |

Without the `refine` table, the phase 4 programs allocate 1,814 GB. A
profile of that revision showed that, in phase 4, the compilation of the
templates into each part of the search space took 37 % of the time, and
the enumeration of the programs 5 %. The `refine` table makes the
compilation cheaper. A check of all the templates in the oracle instead of
the compilation allocated 49 % more.

### Bounded type variables and function buckets

The type search causes the timeouts above. In phases 3 and 4, each type
variable of a constant can take any type of `mtau`. Under a head that
erases its argument type, such as `length :: [a] -> Int`, nothing fixes
the variable. The search then tries instantiations that no term of the
remaining size completes. At HugeLists 7-p3, the size-7 `Int` bucket of
phase 3 listed 19,641 candidates in 2,260 seconds and did not finish. The
two longest stalls, 84 and 90 seconds, were next to
`length (xs >>= foldr (>=>) f fs)` and its `foldl` form.

`--type-depth D` keeps only the types with at most D levels of
constructors and arrows. `--function-buckets` gives a bucket to each
function type between two small data types of the signature.
`--recheck N` tests each new law again on N random cases of sizes 1 to 8,
and drops a law that one of them refutes. All rows use `--recheck 2000`.
The 6-p4 and 7-p3 rows measure `8c44a0d9b` on one core
(`+RTS -N1 -M14G`) with a 900-second limit, as in the main table, with the
same load. On one core, 7-p4 is then inferred to time out. The next row
is the 7-p4 run of the main table. The last two rows keep the earlier
runs of `5c168176d` with `--enumerate-ahead` on 12 cores
(`-N12 -qg -A64m`). Other runs shared the machine during those runs, so
their seconds are upper bounds.

| Configuration | Options | Outcome | Seconds | Allocation GB | Peak RSS MiB | Laws | Dropped by recheck | Completion fallbacks |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| HugeLists-6-p4 | none | complete | 500.9 | 2,015 | 7211.3 | 686 | 26 | 0 |
| HugeLists-6-p4 | `--type-depth 2` | complete | 361.1 | 1,366 | 6042.8 | 671 | 22 | 0 |
| HugeLists-6-p4 | `--type-depth 2 --function-buckets` | complete | 487.4 | 1,927 | 6846.3 | 705 | 22 | 0 |
| HugeLists-7-p3 | `--type-depth 2` | T at 900 s | 900.6 | — | 6019.6 | 584 visible | 55 | 0 |
| HugeLists-7-p3 | `--type-depth 2 --function-buckets` | T at 900 s | 900.6 | — | 6112.6 | 510 visible | 30 | 0 |
| HugeLists-7-p4 | `--type-depth 2` | T (inferred) | — | — | — | — | — | — |
| HugeLists-7-p4 | `--type-depth 2`, `-N12 -qn4 --parallel-tests 64 --speculate 64`, `8c44a0d9b` | complete | 3392.9 | 24,572 | 30667.0 | 1413 | 166 | 5 |
| HugeLists-7-p4 | `--type-depth 2 --enumerate-ahead`, `-N12`, `5c168176d` | complete | 40449.7 | 300,080 | 29748.6 | 1945 | 249 | 81 |
| HugeLists-7-p4 | `--type-depth 2 --enumerate-ahead --split 6`, `-N12`, `5c168176d` | complete | 20816.3 | 167,009 | 29929.1 | 1945 | 249 | 81 |

At 6-p4, the laws are the same as at `5c168176d`: 671 with
`--type-depth 2` and 705 with function buckets, with 22 dropped by recheck
in both. The allocation is 1,366 and 1,927 GB, against 2,216 and 2,960 GB
at `13424d8f9` and 2,337 and 3,130 GB at `5c168176d`. Without a bound,
6-p4 with `--recheck 2000` now completes on one core, in 501 seconds with
686 laws. 7-p3 with `--type-depth 2` prints 584 laws in 900 seconds, as at
`13424d8f9`, against 515 at `2b2d9e562` under a load of 5 to 8: phase 3
takes most of the time at size 7.
At `5c168176d`, 7-p3 with `--type-depth 2` completed on one core in 1,185
seconds with 680 laws, and with function buckets in 2,279 seconds with
686 laws, under a load of 3 to 10.

The first 7-p4 run with `--enumerate-ahead` has no time limit and uses 12
cores (`-N12 -qg -A64m`). It completes in 11 hours 14 minutes with 1,945 laws
(236, 6, 438 and 1,265 in phases 1 to 4). Its maximum residency is
11.9 GB. Phases 1 to 3 take 1,462 seconds, phase 4 sizes 3 to 6 take
5,620 seconds, and phase 4 size 7 takes 32,926 seconds. In size 7, the
tests take about 6,500 seconds. For 26,397 seconds, the thread that tests
waits for the background enumeration of the next type: 700 seconds before
`Int`, 3,440 before `[A]`, 1,655 before `[Int]` and 20,602 before
`[(A,B)]`. Each part of the enumeration is one shape of the left spine
(`--split 2`), and the last part of `[(A,B)]` runs on one thread at the
end. Completion takes 8,508 seconds in all, and 6,956 seconds of that go
to the 80 laws whose completion reaches the 256 GiB budget.

The second run repeats the first with `--split 6`. Each part of the
enumeration is then one shape of the left spine. At `13424d8f9`, phase 4
with `--enumerate-ahead` splits in this way by default. The run completes
in 5 hours 47 minutes. It finds the same 1,945 laws in the same order, and
only the counts of the examined terms change. It allocates 167 TB against
300 TB, and its maximum residency is 10.7 GB against 11.9 GB. Phase 4 size
7 takes 12,569 seconds against 32,926 seconds. In size 7, the tests take
about 6,600 seconds, and the thread that tests waits 5,976 seconds: 532
seconds before `Int`, 3,320 before `[A]` and 2,120 before `[Int]`. The
wait before `[(A,B)]` is gone, because no part is much longer than the
others. Other runs shared the machine at the start of this run, so phase 4
sizes 3 to 6 take 6,210 seconds against 5,620 seconds.

An equational prover checks which laws of the unbounded 6-p4 run follow
from the laws of a bounded run. The check uses twee 2.7.1. Each subterm
carries its type, and `A` to `Acc` are type variables, so a law holds at
each type. Each law gets 10 seconds, and an undecided law gets 60
seconds more. An undecided law can still follow.

| 6-p4 run | Laws | Unbounded laws that follow | Undecided |
| --- | ---: | ---: | ---: |
| `--type-depth 2` | 671 | 676 of 686 | 10 |
| `--type-depth 2 --function-buckets` | 705 | 673 of 686 | 13 |

Most of the ten undecided laws at depth 2 need an instantiation deeper
than 2, for example of `map` at `(A -> [A]) -> [A]` in
`map ((>>=) []) (map (>>=) xss)`. Function buckets do not make these laws
follow. They replace some data laws with function laws, such as
`sum == foldl (+) 0`, from which twee does not derive
`x + sum xs == foldl (+) x xs` within the limit.

With `--function-buckets`, 75 of the 705 laws at 6-p4 are equations
between functions, such as:

```haskell
take 0 == zipWith f []
sum == foldl (+) 0
(++) [] == drop 0
f >=> (g >=> h) == (f >=> g) >=> h
```

A data law cannot state these equations. They also give rules for
unapplied functions, as in `map (take 0) xss`. Each test case applies both
functions to its value of a sample variable of the argument type, as
QuickSpec observes a function. So `--tests` and `--recheck` apply to these
laws as to the others. A first version compared two functions on eight
fixed samples of sizes 1 to 6. At 6-p4 it printed the false
`take 0 == drop 3` and `take 0 == drop 4`, because no sample was longer
than three elements. No number of tests could refute them. The current
version prints neither, and rejects `succ == (+) 1`, which fails at
`maxBound`.

## Differences in laws

24 completed configurations have a completed b530 reference. All 24 retain
its exact ordered numbered law sequence. Printed agreement does not
establish equivalence of every internal Rules basis.

Nineteen completed configurations also retain every stdout byte. Five
completed configurations change only examined-term counters; their ordered
laws, unique-term counts and every other stdout byte match. These differences
are explicitly reviewed, including the adopted size-5 exception. This is
controlled output evidence, not a universal raw-multiplicity theorem.

Printed equality is separate from validity and typed derivability. A smaller
basis can contain more general equations, or omit useful equations. A larger
basis can contain false or redundant equations.

### Lists and polymorphism

Each constant occurrence has its own polymorphic type instance. The checker
accepts `concat []` when the signature supplies `[] :: [A]` and that
occurrence uses `[] :: [[A]]`. It rejects inconsistent repeated parameters,
wrong application result types, and changes to generated-variable types.
Native checked execution retains specialized `Dynamic` application checks.

Fresh packaged native unchecked, native checked and GHC execution produce
exactly the same 24 Lists laws at size 5, phase 4. They include:

```haskell
map f (concat xss) == concat (map (map f) xss)
concat xss ++ concat yss == concat (xss ++ yss)
concat (concat xsss) == concat (map concat xsss)
```

The original Lists7P2 prints this false general form as law 24:

```haskell
map f xs == map f (map f (map f xs))
```

Use `f = succ :: Int -> Int` and `xs = [0]`. The results are `[1]` and
`[3]`. The original carrier wraps `Data.Monoid.Any`, which contains a Bool.
Every total Boolean endomorphism satisfies `f^3 = f`. More tests over that
carrier cannot reject the general claim. Specftacular uses integer carriers.

The complete `cf1bee8f` Lists size-7 outputs at phases 2, 3, and 4 do not
print this form. The check permits consistent variable renaming and equation
reversal. It preserves displayed types and repeated variable identity. The
retained original Lists7P2 prints the form as law 24. This printed-absence
result does not establish that the new Rules cannot derive it.

### Typed law coverage

The preceding f4ec36bd check derives 586 of 597 retained target occurrences
and finds no bounded derivation for 11 independently refuted occurrences.
These were earlier Specftacular corpora, not original Spectacular outputs.
Those proofs do not transfer automatically to a new final Rules basis.

Fresh `cf1bee8f` captures check 597 retained target occurrences against
actual final Rules. The bases contain 41 Lists laws at size 7, phase 4;
197 HugeLists laws at size 5, phase 3; and nine Monad laws at size 6, phase 4.
All 586 ordinary targets are derived. The bounded checker finds no derivation
for the 11 independently refuted occurrences. There are no unknown, missing
or refuted-still-derived results. Targets come from earlier Specftacular
corpora, not original Spectacular outputs; some require type reconstruction.
The larger 305-law and 330-law bases remain outside this selected corpus.

Printed-only reconstruction keeps Given types and repeated identities rigid,
freshens constants per occurrence and infers both sides jointly. Exactly
typed targets retain their labels and annotations. The checker tries raw
typed subsumption in both directions, then normalization, with a two-second
bound per query. No target enters the basis and no extra completion runs.
Missing, failed and timed-out checks remain unknown, including independently
refuted targets. A bounded negative result does not prove non-derivability
or consistency. These controls do not establish equivalence of all 27 bases.
Monad coverage uses size 6, not the size-7 matrix workload.

### Higher-order ListMonad laws

The native resolver composes function generators from a `CoArbitrary`
domain and a generated codomain. It supports `A -> [B]` variables. User
random-generator overrides take priority. Function values receive no
fabricated `Eq` instance. Unsupported generator types produce warnings.
See QuickSpec 2's [generator resolution][qs-generators].

The fresh three-mode Monad size 6, phase 4 control retains nine identical
laws. Its applied forms include:

```haskell
return x >>= f == f x
(xs >>= f) >>= g == xs >>= (f >=> g)
```

QuickSpec 2's [function observation][qs-observe] can compare functions at
generated arguments. By default, Specftacular compares applications. The
applied Kleisli definition and bind associativity imply Kleisli
associativity pointwise, although that exact function equation is not
printed. With `--function-buckets` (see
[Bounded type variables and function buckets](#bounded-type-variables-and-function-buckets)),
ListMonad size 6, phase 4 also prints function laws, among them
`f == f >=> return` and `f >=> (g >=> h) == (f >=> g) >=> h`. Counts
alone do not compare the information in these different bases.

### Regex

At `cf1bee8f`, all three size-7 phase bounds print the same 60 equations.
Their numbered streams match `d2e91fdf` and `102965d3` exactly. General
alternation commutativity is law 8, concatenation associativity is law 25,
and the two distribution laws are 58 and 59. The retained original prints 42
laws and omits those general commutativity and distribution forms. This
comparison concerns printed equations, not complete language equivalence.

The general forms include:

```text
x | y == y | x
x ; (y | z) == (x ; y) | (x ; z)
(x | y) ; z == (x ; z) | (y ; z)
```

The original prints commutativity instances with `any` and `e`, and seven
associativity instances with `any`. Both tools print general concatenation
associativity. Regex equality samples acceptance on 100 fixed words. It is
not exact regular-language equivalence. The QuickSpec artifact has no saved
Regex output for this comparison.

### Representative instances and Octonions

For the same nonnegative gcd signature at term size 3, the original prints
22 laws. The current golden prints six, including general commutativity,
idempotence and the zero identity. The original gives commutativity only at
its constants 1029, 1071 and 21. Testing instances of new representative
schemas recovers the more general result in this example.

Each completed `cf1bee8f` size-7 phase bound prints the same 15 equations as
`d2e91fdf` and `102965d3`. Flexibility is law 8. The middle, left and right
Moufang forms are laws 11, 14 and 15. None of these four displayed forms
occurs in the retained original eight-law output. The saved QuickSpec
artifact also prints 15 equations. Equal counts do not establish equivalent
bases.

Paper section IV-A already explains schema-related differences in Octonion
bases. A different basis or orientation is not itself an error. See
QuickSpec 2's [schema layer][qs-schemas].

### HugeLists and the recorded counterexamples

The native and GHC benchmarks now remove duplicates in `usort`:
`usort [1,1] == [1]`. The published Spectacular definition preserves them.
For finite total lists, `usort (xs ++ xs) == usort xs` is valid for the
current definition but not the published one. The measured signatures
therefore have different meanings.

Two earlier false forms are:

```haskell
take n xs == take n (take (n + n) xs)
length (take 1 (xs ++ ys)) == length (take 1 (zs ++ ys))
```

For the first, `n = maxBound :: Int` and `xs = [0]` give `[0]` and `[]`,
because `n + n` wraps to −2. For the second, `xs = [0]`, `ys = []` and
`zs = []` give lengths 1 and 0.

Machine arithmetic also refutes:

```haskell
sort (map (+ x) xs) == map (+ x) (sort xs)
usort (map (+ x) xs) == map (+ x) (usort xs)
```

Set `x = 1` and `xs = [0,maxBound]`. The sorted left result is
`[minBound,1]`; the right result is `[1,minBound]`. The retained original
HugeLists5P3 prints the sort form as law 133. Its signature uses concrete
Int, not unbounded integers.

`succ maxBound` throws. With `xs = [0,maxBound]`, demanding the first
element of `sort (map succ xs)` throws, while the first element of
`map succ (sort xs)` is 1. The `usort` version has the same difference.
At `xs = [maxBound]`, these three forms also differ under partial-result
observations:

```haskell
map succ xs == map (+ 1) xs
succ (sum xs) == 1 + sum xs
sum (map succ xs) == sum (length xs : xs)
```

The left scalar or first element throws; the corresponding right result is
`minBound`. Full list equality can throw instead of returning False. These
forms are unsafe as unconditional rewrites under non-strict Haskell
contexts. The current complete HugeLists5P3 sequence matches the earlier
197-law corrected output. It omits both take forms and all seven recorded
mapping, sorting and succ forms, including their screened concat inputs.
Printed absence is not proof against every false specialization.

### Six later false equations and the input policy

The `102965d3` HugeLists size 7, phase 2 output printed these five false
predicate equations. Names are shortened; numbers refer to that old output.

| Old law | Equation | Predicate |
| --- | --- | --- |
| 160 | `drop n (dropWhile p (takeWhile q xs)) == dropWhile p (drop n (takeWhile q xs))` | `p = (== 0)` |
| 167 | `drop n (filter p (takeWhile q xs)) == filter p (drop n (takeWhile q xs))` | `p = (== 1)` |
| 175 | `dropWhile p (take n (takeWhile q xs)) == take n (dropWhile p (takeWhile q xs))` | `p = (== 0)` |
| 178 | `filter p (take n (takeWhile q xs)) == take n (filter p (takeWhile q xs))` | `p = (== 1)` |
| 185 | `drop n (takeWhile p (takeWhile q xs)) == takeWhile p (drop n (takeWhile q xs))` | `p = (== 1)` |

For all five, set `n = 1`, `xs = [0,1] :: [Int]` and `q = const True`.
The left side is `[]`; the right side is `[1]`. All values are total.
A supplied predicate can distinguish values even when list operations are
parametric.

Old law 208 is:

```haskell
drop n (drop n (drop n xs)) == drop (n + (n + n)) xs
```

Set `n = div maxBound 2 + 1 :: Int` and `xs = [0]`. On this 64-bit host,
`n` is 4611686018427387904. Triple addition wraps negative. The left side
is `[]`; the right side is `[0]`.

Historical actual-name replays show that all six original/final equations
pass all old 1040 observations in both native modes. No observation throws,
and their decision trees return `EqualTo`. Canonical printed names produce
different seeds and do not reproduce admission. The input failure is a
finite sampling gap, not evidence of skipped validation.

The selected schedule preserves those 1040 cases and appends 24. Sixteen
predicate cases use scalar 1, two-element lists and one distinguishing
predicate for each index residue modulo eight, with other predicates True.
They cover ordered pairs with different residues in Int, A, B, C, D and Acc.
Eight half-range Int cases expose both signs of wrapped triple addition.
Unsupported types request generator size zero in these new cases. A custom
generator can ignore that request; it is not an emptiness or memory bound.
The original 32 boundary cases and their nested extrema inputs remain.

The preceding f4ec36bd HugeLists size 7, phase 2 capture contains 242 laws.
Its bounded checks reject the twelve original/final forms of these six
false targets. Actual-name replays distinguish the old 1040-case prefix
from the new 24 cases. This is revision-scoped evidence.

A fresh `cf1bee8f` HugeLists size 7, phase 2 capture retains all 242 laws.
Bounded checks find no derivation for the twelve original/final typed forms
of the six false targets. Twelve typed witness rows confirm their unequal
results. The 72 schedule groups cover both forms, both native modes, and the
old 1040, new 24 and full 1064 cases. The old prefix treats every form as
equal. This includes the observed law 185 result; it is not assumed. The
new 24 cases and full schedule distinguish every form without exceptions.
Checked and unchecked results agree. No target enters the basis and no
extra completion runs. These bounded checks do not prove non-derivability
or basis consistency.

Finite tests do not prove surviving laws. This input correction is not a
new paper erratum.
Directed values can fall outside custom-generator domains. Distinct predicate
indexes with the same residue remain outside the pairwise guarantee.

## Enumeration, pruning and typed completion

Phase traversal follows paper section III-C. Program leaf sizes increase
first. Type buckets increase by type size, with abstract carriers before
concrete equal-sized types. Canonical annotated KBO orders each bucket.
Rules pass to later phases. Occurrence generalization follows section III-G:
the grammar uses one variable per type, then tests independent assignments,
with more general assignments first. Representative schemas through five
leaves also receive instances, following [QuickSpec 2][qs-schemas]. A
repeated-variable schema is not proof of every renamed equation.

The partial-term oracle follows section III-D. It registers unresolved
matches and resumes them through current union-find representatives. A
proven match rejects a partial branch before remaining choices expand. The
Spec-only fragment guard also checks supported program structure without
waiting for its fixed arrow marker. It requires the stated program/type
encoding and uses the original oracle as fallback.

The new `preparePruning` helper compiles eligible fixed templates into each
supported finite program graph. It preserves opaque annotations and original
edge constraints. One `reducePartially` pass then propagates equalities and
can narrow annotations. The outer oracle keeps templates without a proof
that a compiled pattern covers their complete-term matches. Its remaining
order and duplicates are preserved. Unsupported structure, rejected graph
checks or empty selection return the original graph and full oracle.
Type constructors with the `app/4` encoding disable template pruning. An
exclusion keeps a table of the refinement of a node with its template
parts, so a node that many edges reach is refined once.

Phase 4 enumerates the programs of the skeletons without their type
annotations (`prunedPrograms`). The enumeration expands an annotation only
where a template check waits for it, and a branch stops when only such
holes remain. A typing of the partial program replaces the annotations.
Each new fragment extends it, with each generated variable at the type of
its name, as in the automaton. A fragment without a typing, or a type
variable of a constant with a type deeper than `--type-depth`, ends the
branch. Before each choice, a hole keeps only the constants that can have
its type and the edges whose annotation can hold it. After each typing,
each open hole must keep an edge. A typing only becomes more specific, so
these checks remove only branches that have no typed program.
`generalizeCarriers` types each program again, as before.

Early templates must be linear, well typed and uniformly decreasing.
Repeated variables cannot become independent holes. Erasing annotations
requires principal-type coverage and a decrease independent of annotations.
A covering Hole accepts every subtree; other coverage nodes require the
same symbol, arity and recursive coverage. Typed AnyPrefix is covered only
below such a Hole. Compilation uses the fixed bucket-entry templates,
never later discoveries. The finite-language argument does not prove every
recursive cutoff stream or raw run multiplicity. Graph caps do not bound
transient constructor allocation.

The final bucket sort demands candidates before their first test. New laws
can change later complete-candidate checks but cannot revise enumeration
already done with that bucket's snapshot. Paper section III-E explicitly
uses size/type batching. A fully online ordered extractor is an extension,
not evidence that the published algorithm required another implementation.

Complete rewriting shares term and type substitutions across both sides.
Constant occurrences freshen independently; repeated variables stay rigid.
Rule classification retains both directions unless a decrease survives type
substitution. Actual rewriting checks the instantiated order. Completion
normalization uses uniformly decreasing rules, and ground joinability
requires closed type annotations. These fix port defects, not paper errata.
A direction with unbound right-side variables cannot invent values.

Completion keeps FIFO critical-pair order and the existing leaf/type-depth
budgets. It checks the normalized left size before demanding the right.
A fixed-Rules cache holds at most 256 entries of at most 256 nodes each,
including annotations; larger terms bypass insertion. These are structural
bounds, not byte or termination guarantees. The artifact uses an
[exact rewrite update][original-rewrites] and lists completion as a
[TODO][original-completion-todo], so ordered completion adds work.

Generalization follows [QuickSpec 2's polymorphism layer][qs-poly] and
[type regeneralization][qs-regeneralise]. Shared variables remain shared,
while each constant occurrence gets fresh type binders. Given types and
concrete arithmetic remain rigid. Stronger schemes require the same result
type and comparator, available generators and successful independent-carrier
validation. Unsupported proposals retain the original law. The contract
requires signature constants to be parametric in abstract carriers; they
must not inspect representations or capture class dictionaries. Testing
neither proves a free theorem nor checks every type.

## Validation and current resource tradeoffs

### Size bounds and ordered ground-part groups

The selected private compiler skips templates that cannot fit a program
node's maximum leaf count. It uses Integer bounds from the original finite
program DAG and ignores equality restrictions. The result is an upper bound.
A fixed ordered subset shares its exclusion catalogue across program nodes.
Unsupported graph structure keeps the original graph and complete oracle.

CFTA now builds each ground-part group with Data.Sequence and converts each
used group to a list lazily. Map-key order, row order and duplicate
obligations remain unchanged. The argument requires finite total inputs,
lawful symbol ordering and a group size no greater than maxBound :: Int.
Sequences are strict in their length, so this is not a claim about arbitrary
undefined or infinite lists. See the [containers 0.8 documentation](https://hackage-content.haskell.org/package/containers-0.8/docs/Data-Sequence.html).

The existing prepared-template catalogue retains exact structural keys and
an order embedding. IDs from different catalogues cannot be mixed. The
worker keeps tail-first splitting, keep-before-kill order and guard order.
Conjunctions used only for feasibility do not enter returned obligations.
This adds no global query cache or change to independent-wildcard meaning.

The finite-language result does not imply equal raw multiplicity. In a named
ambiguity control, three input runs represent two annotated terms. Generic
oversized exclusion keeps two runs, while the bound guard keeps three; both
keep the same two terms. Exact-size and Empty controls pass. This shows why
examined counts can change, but does not explain every changed counter or
prove equality of recursive annotation cutoff streams.

The controls pass 16,560 complete raw ordered-copy cases, 16,560 decoded
prepared cases, and 2,387 child/normalization cases. The named finite,
constraint, residual and recursive-annotation controls pass. Existing
goldens pass. All 741 library examples and eight allocation plus eight
Cachegrind cells pass. Four checksum observations agree in each cell. The largest increases against retained b530 are 0.0001594% allocation and
0.0003039% instructions.

| Focused native control | Laws | Wall s | CPU s | Allocated bytes | Peak RSS MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| HugeLists size 5, phase 3 | 197 | 21.37 | 21.382 | 105,927,546,528 | 547.0 |
| HugeLists size 7, phase 2 | 242 | 93.31 | 93.416 | 604,012,145,368 | 923.3 |

Size 5 retains all 197 ordered laws. Only the final examined count changes
from 5833 to 5841; 5217 unique terms and every other stdout byte match. The
raw REVIEW_REQUIRED status remains, with that explicit accepted exception.
Size 7 retains all 242 laws and all 63,004 stdout bytes. These finite controls
do not prove all laws or every recursive cutoff stream equivalent.

Both native controls compile 30 HOME modules at O2: 21 CFTA modules, eight
Specftacular modules and Main. No archived CFTA or Specftacular library is
linked. The native delta combines the private size bound and Sequence. The
library budget contains CFTA/Gen only. Baseline and original processes were
not rerun. These single observations do not estimate timing variance.

### Packaged resource controls

| Completed configuration | Allocation change from `b530f920` | Peak RSS change from `b530f920` |
| --- | ---: | ---: |
| Lists-7-p4 | -6.0908% | -7.0887% |
| ListMonad-7-p4 | -0.7011% | +0.0730% |
| HugeLists-3-p4 | -0.2300% | -8.7743% |
| HugeLists-4-p4 | -1.0065% | -3.0104% |
| HugeLists-5-p3 | -1.7115% | -0.0385% |
| HugeLists-7-p2 | -19.8124% | -16.3209% |

Allocation decreases in all 24 completed configurations, by 0.0400% to
19.8124% against retained b530. This does not imply lower RSS or faster
execution in every configuration.

These changes compare complete searches with the same 1064-case schedule.
The two HugeLists adopted controls compare the same 30-HOME build shape;
other rows compare fresh and retained packaged builds.
Costs can move in different directions; no uniform reduction is claimed.

The earlier `d8986453` Lists size 4, phase 1 control retained all 10 laws.
Its 1.7380% allocation and 1.9235% instruction increases describe that
revision against `d2e91fdf`; they are not fresh `f4ec36bd` measurements.
The older generalization change remains a separate accepted exception:
+15.826% allocation and +17.002% instructions against `456123af`.
The current CFTA validation is reported above.

## Cost-centre evidence and remaining bottlenecks

### Current whole-run profile

The selected size 7, phase 2 profile completes with all 242 laws and every
native stdout byte exact. Its 30 HOME modules use O2 and late cost centres;
automatic/manual source SCC insertion is disabled. No Grammar module or
archived CFTA/Specftacular library is linked. Audited profiling dependencies
remain O2. The 134 provenance files are not 134 linked libraries.

The raw profile has 270,921 ticks. Removing runtime, GC, profiler and
idle self ticks leaves 236,413 application ticks. Each application self
cost belongs to exactly one ancestry group below.

| Observed ancestry | Self ticks | Application share |
| --- | ---: | ---: |
| Private template compiler | 18,673 | 7.8985% |
| Equality reduction outside the compiler | 213 | 0.0901% |
| Other application code | 217,527 | 92.0114% |

The largest individual self centre is `Specftacular.Rewriting.matchesShape`:
33,818 ticks (14.3046%). It checks program structure before
annotation matching. It does not bind variables or inspect annotations.
`edgeCopiesWith` has 7,732 self ticks (3.2705%).
List append beneath that helper has 397 self ticks (0.1679%). These
function costs overlap the ancestry groups; do not add them. Late profiling
can inline or move cost centres. This is stack ancestry, not an exact
account of logical phases. The equality row excludes work charged beneath
the compiler.

The profile takes 270.97 wall seconds and 274.039 RTS CPU seconds. Its wall
time is 2.9040 times the 93.31-second native control. That ratio measures
profiling distortion, not a native gain. RTS allocation is 1,238,537,187,216
bytes; cost-centre allocation is 742,872,047,200 bytes. Peak RSS is
1,617,692 KiB. These are whole-profile process costs, not native or
selected-window costs.

### Experiments tried

These controls use HugeLists size 7, phase 2. The retained `b530f920`
baseline allocates 753,249,161,232 bytes. Every variant preserves
its complete 242-law stdout stream. Each comparison names its denominator.
Some size-5 examined counters changed. Those differences were reviewed
separately; laws and unique-term counts remained unchanged.

| Experiment | Allocation comparison | Decision |
| --- | --- | --- |
| Retained `b530f920` | Baseline | No baseline process rerun. |
| Persistent grammar bank | 2.858 times b530 | Rejected. Reusing pruned child roots added compilation work. |
| Bank with batch sharing | -0.7303% vs initial bank | Rejected. Allocation remained 2.837 times b530. |
| Size bound alone | -19.1157% vs b530 | Selected with Sequence. |
| Bank plus size bound | +24.0841% vs size bound alone | Rejected. The bank still added work. |
| Certified bank with residual checks | +23.6327% vs size bound alone | Rejected. Removing certified repeated checks did not remove the bank cost. |
| Repeated-ID splitting fast path | -0.8780% vs b530 | Not selected. No observed timing win. |
| Direct-cons splitting | No material change vs b530 | Not selected. |
| Prepend/reverse ground-part groups | -5.0457% vs b530 | Alternative to Sequence. |
| Sequence ground-part groups | -4.3802% vs b530 | Selected with the size bound. Keeps insertion order directly. |
| Sequence plus size bound | -19.8124% vs b530 | Selected `cf1bee8f`. |

Sequence alone allocates 0.7009% more than the prepend/reverse
variant. It expresses insertion order directly. Allocation was the main
selection measure. These are single O2 controls with accepted concurrent
load, so their timings do not estimate variance. The current runtime has no
Grammar module or persistent-bank flag. Finite controls do not prove equal
raw multiplicity or recursive cutoff behavior for every input.

Three later controls use HugeLists size 5, phase 3 at `2b8275c4`. Each
variant prints the same 197 laws and the same stdout bytes. A repeated
baseline run allocates the same number of bytes.

| Experiment | Allocation comparison | Decision |
| --- | --- | --- |
| A missing variable raises `IllTyped`, with `case` on `Map.lookup` | +0.2728% vs `2b8275c4` | Selected. A missing value no longer becomes `Untested`. |
| The same check with `Map.findWithDefault` | +0.6819% vs `2b8275c4` | Not selected. |
| Two-list completion queue | -0.0003% vs the `findWithDefault` check | Selected. An append no longer walks the queue. |
| Tables of the boundary and predicate values | -0.0746% vs the `findWithDefault` check | Not selected. The gain is too small for the extra code. |

The remaining ordered-frontier alternative is described under
[Further algorithmic work](#further-algorithmic-work).

Earlier f4ec profiles located structural-template comparison work. Its
normalization census found repeated wanted parts, but did not measure
reuse of complete query keys. Carried identifiers already address that
representation cost. Those historical percentages are not current hotspot
measurements. The current whole-run profile does not locate the remaining
timeouts; they require their own phase and cost-centre evidence.

### Preceding one-hour controls

The preceding `b530f920` runtime also has two closed one-hour trials,
with a 32 GB cgroup cap and 24 GiB Haskell heap limit. HugeLists size 6, phase 4 times out with 436 complete visible equations and
3,316,576 KiB peak RSS. Size 7, phase 3 times out with 380 complete visible
equations and 2,291,084 KiB peak RSS. Size 7, phase 4 was not run because its
earlier-phase prerequisite did not complete. These are preceding-runtime
controls, not current matrix rows or a timing comparison with this revision.
Buffered timeout prefixes are lower bounds, not final law counts.

## Memory and allocation

QuickSpec 2's sparse [decision tree][qs-tree] retains counterexamples that
separate representatives. The current engine follows that design. A leaf
retains a term evaluator. A branch retains one discriminator case and its
values. Test cases store seeds and boundary indexes. Each comparison
generates only the variables used by either term. Both evaluators use the
same valuation for that case. The tree retains a valuation only through
discriminator values. It does not retain all generated nested lists and
complete result vectors at every representative.

A historical 29-law Lists5P4 control changed retained input/result vectors
to sparse evaluation. Peak RSS fell from 1920.5 to 51.4 MiB; allocation
changed from 20.93 to 20.59 GiB. That control also changed comparison order
and can treat partial values differently. It does not isolate storage alone
or predict current large-search memory. Current memory is measured below.

Fresh packaged `cf1bee8f` memory controls:

| Control | Native unchecked MiB | Native checked MiB | GHC MiB |
| --- | ---: | ---: | ---: |
| Lists5P4 | 53.9 | 57.8 | 541.2 |
| ListMonad6P4 | 87.8 | 84.8 | 549.1 |

The modes retain the same 24-law Lists and nine-law Monad sequences. The GHC
process includes the compiler and interpreter. Agreement does not prove
coverage equivalence.

Across current matrix processes, maximum observed RSS is 2522.5 MiB
(HugeLists-6-p4, actual 900-second guard). Adopted controls remain
explicitly labelled. Timeout resources are censored. Allocation is
cumulative traffic, and missing RTS totals remain unknown.

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
`--checked` does not add `Dynamic` application checks to those
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

## Further algorithmic work

1. **Avoid repeated typed matching and branch expansion where measured.**
   The current completed size-7 profile puts 14.3046% of application self
   ticks in `matchesShape` and 7.8985% in compiler ancestry.
   Profile the unfinished configurations before treating either as their
   bottleneck. Test an index or local exact-query cache only against fixed
   work and complete outputs. Preserve repeated variables, rigid Given
   types, occurrence freshness, order and the original fallback. Faster
   random generation alone does not achieve early template pruning.

2. **Share exact exclusion work only when a census demonstrates reuse.**
   Count distinct ordered obligations, source identity, recursion context
   and peak live state without forcing unused children. A prepared plan
   could share a catalogue and product states across supported roots.
   This remains a proposal. Use the existing `restrictFTA`, `excludeFTA`
   and `excludeAnywhereFTA` contracts. Keep equality obligations for repeated
   variables and constrain typed branches before enumeration. Preserve raw
   order and residuals separately; return the original graph and oracle when
   coverage is unknown. Generic exclusion can merge ambiguous runs.

3. **Certify canonical annotated KBO prefixes.** `ExpansionOrder` selects
   an already ready UVar. It cannot partition correlated program/type
   choices or certify an unpulled sibling suffix. A stronger design needs
   an inspectable constrained witness relation and certified minima.
   Preserve stable equal-key ties, rigid Given identities, occurrence
   freshness, constraints and recursion context. Unknown feasibility cannot
   mean empty. One arbitrary principal instance cannot replace the complete
   witness relation. Annotation cycles need a termination argument if their
   positive size cost is removed.

These further changes are not implemented. Keep phase, size and type order,
generalization, validation and the original oracle fallback. Require exact
ordered helper outputs, annotated/residual controls, complete law streams
and library budgets. Construction budgets must return Unknown and the
original graph before unbounded work. Stronger pruning still requires valid
laws under the selected comparator; finite tests do not prove them.

The Amendments section concerns the published artifact and paper.

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

`--type-depth` omits the laws that need a deeper instantiation, and the
completion consequences of those laws. `--function-buckets` covers only the
function types between data types of size at most two. It compares two
functions on one sample of the argument type in each test case, so the
test of a function law depends on the generator of that type.

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

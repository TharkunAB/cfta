# The Lean spike: directions and work in progress

## Generalized refinements, 2026-10-20

The current branch is `spike/refinement-logic` in
`~/Code/microecta/lean-kimina`. The [generalized refinement spike](lean-spike-generalized.md)
extends the Kimina checkpoint with named types, interpreted functions and
predicates, and exact partial solver lowering. It now builds on PR #89 and
stores the language and its logical context for replay. Read that document first.
The sections below record earlier checkpoints.

## Restart with Kimina, 2026-10-20

This section supersedes the runtime plan below. The earlier notes and
measurements remain as historical evidence.

The worktree is `~/Code/microecta/lean-kimina`, on `spike/lean-kimina`.
It starts at cfta main `9769fe3e` and merges the previous `lean-spike`
checkpoint `3ab4caa6`. Main already contains newer versions of the shared
synthesis code. The merge keeps those versions.

The requested direction is Lean as an LTA solver, behind `Entailment`.
Use standard Kimina and check complete proof candidates in batches.
Do not extend Kimina with a stateful transport or add a synthesis tactic.

The active `cfta-lean` package implements this direction:

- `Data.CFTA.Lean.withKimina` sends the closed implication and its negation
  to `/api/check`. A checked proof determines `Yes` or `No`. Failure to
  obtain either proof gives `Unknown`.
- `Data.CFTA.Lean.Formula` translates the supported formula subset and
  validates sorts, arities, and bindings. Source names never become Lean
  source identifiers.
- `fallback` preserves the Z3 result and calls Kimina only on uncertainty
  or a Z3 time limit.

The old process, tactic, executable, and benchmark are in the merged branch
history. They are not part of the active package. The package's existing
test suite now exercises the solver. No core cfta algorithms change.

The local service uses Kimina 2.0.0 and Lean/Mathlib 4.26.0 at
`http://127.0.0.1:8000`. Its systemd limit is 16 GiB, with no swap. The old
Lean 4.35.0 tactic results do not describe this runtime.

Validation on this checkout:

- Strict GHC 9.14.1 build and all 16 existing test cases pass against the
  local Kimina service. The tests include an LTA semantic guard.
- A separate HTTP fixture probe passes 28 checks. It covers invalid replies,
  unfinished proofs, result IDs, HTTP failures, and the actual HTTP timeout.
  It also checks that unsupported formulas make no request and that the
  client does not execute Lean.
- Six additional formula checks give `Yes` through Kimina. Negative integer
  division, negative remainders, conditionals, and Boolean functions agree
  with Z3. Two quantified cases give `Unknown` through current `withZ3`.
- Build and probe runners use memory caps. The final build scope reports
  8 GiB for both memory limits and zero swap. Haskell test heaps use 1 GiB.

### Verified fallback example

For every integer `x`, the condition `exists y : Int, y = x` holds. Therefore
`if (exists y : Int, y = x) then 7 else 9` equals 7. The existing test suite
contains the formula:

```haskell
let condition = Exists [("y", IntSort)] (Atom Eq (Var "y") (Var "x"))
    conclusion = Atom Eq (Ite condition (Lit 7) (Lit 9)) (Lit 7)
in entails (fallback z3 lean) Top conclusion
```

On this host, Kimina gives `Yes`, `withZ3 []` gives `Unknown`, and the
combined solver gives `Yes`. Liquid Fixpoint disables Z3's `smt.mbqi` and
`auto-config`. A direct incremental SMT query decides this formula with
Z3's defaults. Disabling `smt.mbqi` reproduces `Unknown` with reason
`(incomplete quantifiers)`. Disabling only `auto-config` still decides it.
This example establishes a fallback for the current configuration. It does
not establish that Lean solves a problem beyond Z3's capabilities.

### Remaining work

- Broaden proof search only with measured examples. In particular, the
  four old nonlinear examples do not all pass the fixed tactic portfolio
  on Lean 4.26.0.
- Reals, casts, nonliteral or nonpositive divisors, defined measures, and
  data sorts are unsupported. They give `Unknown`.
- Remote authentication, HTTPS configuration, and a hosted Kimina CI job
  are not configured. Ordinary CI builds the package and runs its local
  boundary tests; live tests require `CFTA_KIMINA_URL`.

## Historical spike notes

The spike stopped on 2026-10-15. This branch, `lean-spike`, is
`spike/states-automaton` (`16ef6d6a`) with these notes. It holds the generic
modes of TharkunAB/cfta#10, the cfta-lean package of TharkunAB/cfta#11, and
the automaton path of mode (b). The notes of the earlier steps stay beside this
file: `docs/host-checkers.md` (one design for GHC and Lean, and the cost
cascade) and `docs/host-agnostic-modes.md` (the portfolio and mode (b), as
designed and as built). The small result files are in `docs/lean-spike/`.

## Direction, current: Lean as an LTA solver behind `Entailment` (draft)

This part is a draft. It was written before any code, and it is not
reviewed.

### The aim

Matti, 2026-10-15: "we need to retool cfta-lean. We got it all upside down,
the idea was to be able to use lean as a solver (think z3) in LTAs, not to
introduce a tactic". So Lean is to be a second solver, beside Z3, for the
semantic questions of liquid tree automata.

### The seam

Every semantic question of an LTA goes through `Entailment` in
`Data.CFTA.Refinement.Verdict`:

```haskell
entailsWithBindings :: [(Name, Name)] -> Formula -> Formula -> IO Verdict
data Verdict = Yes | No | Unknown
```

- `Formula` (`Data.CFTA.Formula`) has `Top`, `And`, `Bottom`, `Or`, `Not`,
  `Atom` (`Eq`, `Ne`, `Gt`, `Ge`, `Lt`, `Le`), `Forall`, and `Exists`.
  `Term` has integer literals, names, applications of uninterpreted functions
  (`App`), `Neg`, `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Ite`, and `Cast`.
  `Sort` has `IntSort`, `RealSort`, `BoolSort`, and `FunctionSort`. There is
  no sort of data, and a function has no definition.
- A named measure reaches the solver as an uninterpreted `App`, declared by
  its arity. Hegel's measures (`len`, `hd`, `lst`, `mem`, `at`, ...,
  `cfta-generator/common/Data/CFTA/Gen/Synthesis/HegelBenchmarks.hs`) are
  such functions on integers.
- Z3 (`Data.CFTA.Refinement.LiquidFixpoint`: `withZ3`, `withZ3Assuming`,
  `withZ3Timeout`) runs as one process for many queries, with one scope (push
  and pop) for each query. Each query sends its declarations, asserts the
  ambient assumptions, the antecedent, and the negated consequent, and checks.
  Unsat gives `Yes`, sat gives `No`, and unknown gives `Unknown`, or the
  exception `TimeLimitReached` when the check took the whole limit
  (`defaultTimeLimit`, 10 s).
- The lattice (`Data.CFTA.Refinement.Lattice`) is another `Entailment`: it
  counts the integer points of linear formulas, and it answers `Unknown` for
  an unbounded variable or a non-linear term.

### `No` is necessary

Pruning (`PruneUnknown`), minimization (`SimilarityUnknown`), the denotation
(`DenotationUnknown`), the guards of `Data.CFTA.Sized` (`GuardUnknown`), and
the compiler of LTA generators (`SolverUnknown`) all fail on `Unknown`. They
need `Yes` or `No` for each question. So a solver that gives only `Yes` and
`Unknown` helps only where it turns an `Unknown` of Z3 into `Yes`; to help
these operations everywhere, it must also answer `No`.

### What Lean adds

- **Non-linear integer facts** that Z3 can give up on. Candidate examples,
  in the current `Formula`: `(x*x - x) % 2 = 0`,
  `(x*x) % 4 = 0 ∨ (x*x) % 4 = 1`, `(x*x*x - x) % 6 = 0`, and
  `x > 0 ∧ y > 0 → x*y ≥ x`. They are written for Z3 4.15.3
  (`docs/lean-spike/examples/e1.smt2` to `e4.smt2`, with the 10 s limit) and
  for Lean 4.35 (`docs/lean-spike/examples/Examples.lean`, with `grind` and
  `simp`). They were not run: the run waited for the shared machine, and the
  spike stopped first. Each example still needs both results before it can
  stand in a note.
- **Definitions**: measures with bodies, recursive functions, and inductive
  types, for example `len (xs ++ ys) = len xs + len ys` with `List.length`.
  This needs `Formula` to grow: a sort of data (an uninterpreted sort for Z3,
  a Lean type for Lean), and a map from function names to Lean definitions.
  Z3 then treats the defined functions as uninterpreted. Its `Yes` stays
  sound, because it holds for every interpretation. Its `No` does not, because
  its countermodel need not respect the definitions.

### How Lean can answer `No`

Lean proves; it does not find models. The options are:

1. Z3's model, checked in Lean by evaluation of the definitions on the
   model's values;
2. `decide` on finite domains (`Bool`, `Fin n`, bounded integers);
3. `Unknown` otherwise.

### Transport and cost

The `lean-oracle` process of cfta-lean (`feature/cfta-lean`, `d6cfb4c4`) is
the transport: it starts once, imports the modules named on its command line
(the user's definitions as Lean modules), and answers tab-separated requests
on its standard input and output. A solver adds one request, "decide this
entailment", with the formula as data (not as text to elaborate), and a
heartbeat limit for each query. A round trip over the pipe costs about
0.1 ms, and the tactic's time comes on top. Most Z3 queries cost well under a
millisecond. So the useful form is a portfolio: Z3 first, Lean on `Unknown`.

### Acceptance

- The LTA cells and Hegel's 42 queries give the same results with Lean behind
  Z3. (The comment in `Data.CFTA.Gen.Refinement.Internal.Witness` says that
  the test suite and the benchmark cells give no `Unknown` today, so there
  Lean is not asked.)
- At least one example that Lean decides and Z3 does not.

## Direction, mode (b): one automaton for each size

The table of states of mode (b) is a tree automaton: the states are nodes, the
refinements are edges, and the child goals are the children. The direction
is one interned cfta automaton for each size, with a Template exclude in place
of the walk of the trie of dead prefixes. An exclude operation for Templates
is in work elsewhere; cfta has no complement today.

### What is built

- `searchStatesWith :: Walking -> ...` in `Data.CFTA.Gen.Synthesis.States`.
  `Walking` is `Preorder` (the depth-first search of #10) or `Enumerated
  EdgeOrder`; `EdgeOrder` is `CanonicalOrder` (`runs`) or `HostOrder`
  (`runsBy`, with the place of each edge in its state as its weight).
- `Enumerated` builds the automaton of the states that the root reaches: a
  node for each state, and an edge for each transition and split, labeled by
  the leaf's name. Each listed program goes through Hectare's rule for the
  first argument, the trie of dead prefixes, and the walk's checker.
- `figuresCount`: the programs of the automata, counted exactly with
  cfta-generator's `cardinality` of `fromAutomaton`.
- The `States` mode of cfta-ghc and cfta-lean carries the `Walking`; the
  benchmarks read `automaton` and `automaton-canonical`. The tests: the
  generic test gives the same programs through the automaton, and cfta-lean's
  test fills its goal through it with the oracle.

### The checkpoint

One shared run (12:02 to 12:23, with other jobs on the machine), so the
seconds only indicate. GHC: Hoogle+ rungs 1 and 2, 120 s, 8 pinned children.
Lean: core (index) and sweep (index, head). "states" is the depth-first
search of #10, and "automaton" the automaton in the host's order. The
summary is `docs/lean-spike/compare.txt`, from `docs/lean-spike/compare.py`.

| | GHC rung 1 | GHC rung 2 | Lean core | Lean sweep |
| --- | --- | --- | --- | --- |
| solved, states / automaton | 23 / 23 | 34 / 34 | 22 / 22 | 18 / 18 |
| solved sets | the same | the same | the same | the same |
| first fit | the same, 45 of 45 | the same, 45 of 45 | the same, 22 of 22 | the same, 22 of 22 |
| rank of the expected program | the same, 22 of 23 | the same, 33 of 34 | the same, 22 of 22 | the same, 18 of 18 |
| solver calls on the solved queries | 441,186 / 441,249 | 1,004,301 / 1,004,530 | - | - |
| programs checked on the solved queries | 674,997 / 675,056 | 1,334,004 / 1,334,324 | 282,852 / 279,103 | 141,822 / 141,649 |
| programs in the automata (exact) | 16,161,926,565 | 4,256,649,795 | 2,713,666 | 51,992,460 |
| seconds on the solved queries | 47.7 / 72.8 (+53%) | 131.6 / 117.0 (-11%) | 42.0 / 42.8 (+2%) | 39.1 / 40.0 (+2%) |

- The host's order gives the same checks as the depth-first search. The rank
  changes (`zipWithResult`: 82 to 91 on rung 1, 96 to 105 on rung 2) have two
  causes: interning merges identical edges, so the duplicate runs of #10's
  search go (`flatten` checks 7 programs, not 19), and an edge that two states
  share gets its weight from its place in the first state.
- The cost is the listing of the programs under dead prefixes, one by one,
  which the depth-first search leaves at once. In a pinned smoke run
  (`headLast`, 60 s), the listing took 2.4 s against 0.7 s, and the checks
  took the same time.
- The canonical order loses: in the smoke run, the expected program of
  `appBoth` falls from rank 1 to 195, and `headLast` runs out of time.
- No exclusive timing run took place, so GHC's time is not settled.

### Open item

`termsPruneWith` can prune a branch inside cfta's enumerator, but its oracle
is pure (`EnumerateM`), and the checker's verdicts come from `IO` or `TcM`. An
oracle could read the trie of dead prefixes through `unsafeDupablePerformIO`;
the trie only grows, so the pruning stays monotone. This option was ruled out
for now.

## Dropped: the `hectare?` tactic

cfta-lean had a tactic, `hectare?` (`Oracle/Tactic.lean`,
`Oracle/Suggest.lean`, and the `hectare-propose` executable): a portfolio of
mode (a) and the oracle's own search over states, which closed a goal and
suggested programs as `exact?` does. TharkunAB/cfta#11 is closed, because Lean
is to be a solver for LTAs, not a tactic. TharkunAB/cfta#10 is closed for the
design of an automaton for each size with a Template exclude.

What a solver can reuse of #11 (`feature/cfta-lean`, `d6cfb4c4`):

- the `lean-oracle` process: its start, the imports from its command line,
  the `ready` line with the import time, and `maxHeartbeats` in its
  `Core.Context`;
- the line protocol (`Oracle/Session.lean`): one tab-separated request on a
  line, one reply, and `error` for a request that fails;
- the Haskell client's process handling (`withOracle`, the requests and
  replies, `missingOracle`), and the tests and CI that skip without Lean;
- `elaborateType` and the entry into a goal's binders, for definitions that
  come as Lean text.

## Work in progress, and where it stops

| Branch | Head | What it is |
| --- | --- | --- |
| `lean-spike` | this commit | these notes, on `spike/states-automaton` |
| `spike/states-automaton` | `16ef6d6a` | mode (b) as an automaton for each size |
| `feature/cfta-lean` | `d6cfb4c4` | TharkunAB/cfta#11, closed: cfta-lean, the oracle, the tactic |
| `feature/host-agnostic-modes` | `e7ff4f85` | TharkunAB/cfta#10, closed: the portfolio and mode (b) |
| `spike/host-agnostic-modes` | `148b5cb8` | steps 1 and 2 of the generic modes, before the PRs |
| `spike/lean-oracle` | `56025b5c` | the first Lean spike: the oracle, the cascade, the tactic |

The result files kept here, in `docs/lean-spike/`:

- `compare.py` and `compare.txt`: the comparison of the checkpoint above;
- `portfolio2.keep`: `hectare?`'s portfolio against `exact?` on 22 queries;
- `stage3a.out`: the first Lean benchmark stage (the round trip, `exact?`);
- `STATUS-lean.md`: the status file of the spike, step by step;
- `examples/`: the candidate examples for a Lean solver, not yet run.

The other result files stay outside the repository: the rows of the GHC
ladders and the Lean suites of each step.

### Lean API traps

- `unsafe enableInitializersExecution` must come before
  `importModules (loadExts := true)`.
- A standalone process sets `maxHeartbeats := 0` in its `Core.Context`.
- `isDefEq` needs `approxDefEq` for `?f ?b =?= Option b`.
- `partial`, `variable`, and `using` are keywords, not names.
- Inside a tactic, a search's heartbeats count against the enclosing
  elaboration even with `maxHeartbeats := 0`, so the search stops at nine
  tenths of the limit.
- `findSysroot` needs `lean` on the `PATH` (elan) or `LEAN_SYSROOT`.
- The locals that are type formers (`m : Type → Type`) are not leaves.
- `levelZero`, `levelOne`, and `insertCore` are deprecated: use `Level.zero`,
  `Level.one`, and `insertKeyValue`.
- The Haskell client's `-threaded` runtime adds about 20 µs to each round
  trip over a pipe.
- An unoptimized `hectare-propose` does not meet the tactic's 2 s for mode
  (a), so the tactic's tests need `-O2`.

## Open questions

- Which extension of `Formula` (a sort of data, a map of definitions) gives
  Lean its definitions, and how does a user name them?
- Does Z3's `Yes` stay usable when some functions have Lean definitions?
- How does Lean answer `No`: Z3's model checked by evaluation, `decide`, or a
  property tester?
- Which LTA cell or Hegel query reaches `Unknown` on Z3 today, if any?
- What does `RealSort` become in Lean, without Mathlib?
- What heartbeat and time limits does a Lean query get, and does a cache of
  verdicts help?
- Does the oracle process serve both the solver and synthesis, or only the
  solver?
- What does a Template exclude cost, against the walk of the trie of dead
  prefixes?
- What is GHC's time for the automaton path on a quiet machine?
- Can `termsPruneWith` take an effectful oracle without `unsafePerformIO`?

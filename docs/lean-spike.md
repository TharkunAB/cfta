# The Lean spike: where it stands

State on 2026-10-15 12:51, when the spike stopped. The branch `lean-spike` is
`spike/states-automaton` (`16ef6d6a`) with this file.

## Directions

- **Lean as an LTA solver behind `Entailment`.** Matti (2026-10-15 11:5x): the
  aim of cfta-lean is Lean as a solver in LTAs, as Z3 is, not a tactic.
  The seam is `Entailment` in `Data.CFTA.Refinement.Verdict`
  (`entailsWithBindings :: [(Name, Name)] -> Formula -> Formula -> IO Verdict`).
  The draft note below is the starting point.
- **Mode (b) as an automaton for each size.** The table of states of mode (b)
  of #10 is a tree automaton: states are nodes, refinements are edges, and
  child goals are children. The spike on this branch builds one interned cfta
  automaton for each size and lists it with cfta's enumerator in the host's
  order. It gives the same solved sets and first fits as #10's search, and
  exact counts, ranks, and sampling of the over-approximation. Its cost is the
  listing of the programs under dead prefixes, which #10's search leaves at
  once. A Template can restrict the automaton to the programs under a prefix,
  but it cannot exclude the dead prefixes, because cfta has no complement.
  Pruning inside the enumerator (`termsPruneWith` with the trie of dead
  prefixes) needs an effectful oracle; `unsafePerformIO` was ruled out.

## Draft: cfta-lean as an LTA solver (not finished)

What the seam is, from the code:

- `Formula` (`Data.CFTA.Formula`) has `Top`, `And`, `Bottom`, `Or`, `Not`,
  `Atom` (`Eq`, `Ne`, `Gt`, `Ge`, `Lt`, `Le`), `Forall`, and `Exists`.
  `Term` has integer literals, names, applications of uninterpreted
  functions (`App`), `Neg`, `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Ite`, and
  `Cast`. `Sort` has `IntSort`, `RealSort`, `BoolSort`, and `FunctionSort`.
  There is no sort of data, and a function has no definition.
- Z3 (`Data.CFTA.Refinement.LiquidFixpoint`): one reused process, one scope
  (push and pop) for each query, the declarations sent with each query, and
  the ambient assumptions of `withZ3Assuming` in the scope. Unsat gives
  `Yes`, sat gives `No`, and unknown gives `Unknown`, or the exception
  `TimeLimitReached` at the limit (`defaultTimeLimit`, 10 s).
- Exactness needs `No`: `Unknown` is an error in pruning (`PruneUnknown`),
  minimization (`SimilarityUnknown`), denotation (`DenotationUnknown`), the
  guards of `Data.CFTA.Sized` (`GuardUnknown`), and the compiler of LTA
  generators (`SolverUnknown`). So a solver that gives only `Yes` and
  `Unknown` helps only where Z3 answers `Unknown`.
- The LTA examples keep their guards local and integer
  (`cfta-generator/examples/SortedLists.hs`: the element is at most the
  head of the rest), and the lattice (`Data.CFTA.Refinement.Lattice`) counts
  linear integer formulas without a solver. Hegel's measures
  (`cfta-generator/common/Data/CFTA/Gen/Synthesis/HegelBenchmarks.hs`: `len`,
  `hd`, `mem`, ...) are uninterpreted functions on integers.

What Lean adds, and what it needs:

- With the current `Formula`, Lean can decide what Z3 gives up on, as some
  non-linear integer facts (`grind`, `omega`, `decide`, `simp`). Candidate
  examples, written down and not yet run: `(x*x - x) % 2 = 0`,
  `(x*x) % 4 = 0 ∨ (x*x) % 4 = 1`, and `(x*x*x - x) % 6 = 0`. The files are
  in the scratchpad (`lean-solver/smt/*.smt2` for Z3,
  `lean-solver/lean/Examples.lean` for Lean).
- Lean's real gain is definitions: measures with bodies, recursive
  functions, and inductive types (`len (xs ++ ys) = len xs + len ys` with
  `List.length`). That needs `Formula` to grow: a sort of data (an
  uninterpreted sort for Z3, a Lean type for Lean), and a map from function
  names to Lean definitions. Z3 then treats them as uninterpreted. Its
  `Yes` stays sound, but its `No` does not, because its countermodel need
  not respect the definitions.
- `No` from Lean: Lean finds no models. The options are: Z3's model checked
  by evaluation in Lean; `decide` on finite domains; or `Unknown`.
- Transport: the `lean-oracle` process and its line protocol of
  `feature/cfta-lean` (`d6cfb4c4`), with a request for one entailment, the
  user's modules as imports, and a heartbeat limit per query. A Lean query
  costs about 0.1 ms of round trip plus the tactic's time, against well under
  a millisecond for most Z3 queries. So the useful form is a portfolio: Z3
  first, Lean on `Unknown`.
- Acceptance (to keep): the LTA cells and Hegel's 42 queries unchanged with
  Lean behind Z3, and at least one example that Lean decides and Z3 does not.
- From #11 (closed, branch kept): the oracle process, its protocol, its
  imports, and the erasure are reused. The tactic (`Oracle/Tactic.lean`,
  `Oracle/Suggest.lean`), the proposer executable, and the synthesis
  benchmark are not needed by the solver.

## Work in progress and branch heads

| Branch | Head | State |
| --- | --- | --- |
| `feature/host-agnostic-modes` | `e7ff4f85` | TharkunAB/cfta#10: the generic modes (portfolio, mode (b)), gated |
| `feature/cfta-lean` | `d6cfb4c4` | TharkunAB/cfta#11, closed: cfta-lean, the oracle, the tactic |
| `spike/states-automaton` | `16ef6d6a` | mode (b) as an automaton for each size, measured on a shared machine |
| `spike/host-agnostic-modes` | `148b5cb8` | the spike with steps 1 and 2, `docs/host-agnostic-modes.md`, `STATUS-lean.md` |
| `spike/lean-oracle` | `56025b5c` | the first Lean spike, `docs/host-checkers.md` |

The automaton spike's results: GHC rungs 1 and 2 and Lean core and sweep,
the same solved sets (23, 34, 22, 18) and first fits as #10's search; ranks
the same except `zipWithResult` (82 to 91, and 96 to 105); Lean's time within
2%. GHC's time is not settled (+53% and -11% on a shared machine). The files
are in the scratchpad: `states-automaton/ghc-{states,automaton}-{prelude,base}.csv`,
`states-automaton/lean-{states,automaton}-{core,sweep}.out`,
`states-automaton/compare.py`, and `states-automaton/smoke.log`.

Not done: an exclusive timing run of the automaton spike, the runs of the
candidate examples on Z3 and Lean, and the design note itself.

## Lean API traps

- `unsafe enableInitializersExecution` must come before
  `importModules (loadExts := true)`.
- `maxHeartbeats := 0` in the `Core.Context` of a standalone process; inside a
  tactic, a search's heartbeats count against the enclosing elaboration even
  with `maxHeartbeats := 0`, so the search stops at nine tenths of the limit.
- `isDefEq` needs `approxDefEq` for `?f ?b =?= Option b`.
- `partial`, `variable`, and `using` are keywords, not names.
- `findSysroot` needs `lean` on the `PATH` (elan) or `LEAN_SYSROOT`.
- The locals that are type formers (`m : Type → Type`) are not leaves.
- `levelZero`, `levelOne`, and `insertCore` are deprecated: use `Level.zero`,
  `Level.one`, and `insertKeyValue`.
- The Haskell client's `-threaded` runtime adds about 20 µs to each round trip
  over a pipe.
- An unoptimized `hectare-propose` does not meet the tactic's 2 s for mode (a),
  so its tests need `-O2`.

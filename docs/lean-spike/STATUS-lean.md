# Lean spike: status

Branch `spike/lean-oracle`, worktree `~/Code/microecta/spike-lean`, rebased
on `origin/microcfta` `7bfb69d1` (#129, the packages renamed to `cfta`,
`cfta-generator`, `cfta-ghc`, and `cfta-lean`) on 2026-10-14 21:46. The
host-agnostic modes are on `spike/host-agnostic-modes` (worktree
`~/Code/microecta/host-modes`), which starts from it. Not pushed.

## Assumptions

- One oracle process per query, as the GHC benchmark has one child per
  query. The oracle imports `Init` only: Lean core without `Std` and
  without Mathlib.
- The query types bind their type parameters in `Type` (universe 0), as
  `∀ {α : Type} [BEq α] (x : α) (xs : List α), Nat`.
- `HAdd.hAdd` (`+`) has the erased type `a -> b -> c`, a result of any type,
  so it is left out, as on the GHC side. The `[Add α]` queries use `Add.add`.
- Hectare's "use every argument" rule holds for the Hectare walk. The `exact?`
  baseline gets the same rule from `exact? using` (all explicit arguments
  required), and also runs without it.
- No defaulting: a program whose instance problem keeps a metavariable at the
  end does not fit (`List.length []` is ambiguous), as on the GHC side.

## Stage 1: a Lean `MetaM` checker, end to end (done 14:47)

`cfta-lean/oracle`: a Lake project (toolchain `leanprover/lean4:v4.35.0`)
with the executable `lean-oracle`.

- `Oracle/Erase.lean`: Lean types to Hectare's first-order types.
- `Oracle/Walk.lean`: the step (`mkConstWithFreshMVarLevels`, binder-by-binder
  instantiation, `isDefEq`, `synthInstance?` on ground instance problems), the
  frame stack with `saveState`/`restore`, and the complete check
  (`instantiateMVars`, `Meta.check`).
- `Oracle/Session.lean`: the tab-separated line protocol.

A hand-written stream (a Python driver, not kept, 9 programs for
`countElem`) gave the expected verdicts: `List.count x xs` fits,
`List.count xs x` dies at token 2, `List.length List.nil` does not fit
(ambiguous), and the prefix sharing (`extend 2 ...`, `extend 4 ...`) gives the
same fit. Figures from that run:

| Figure | Value |
| --- | ---: |
| import of `Init` | 123 ms |
| `isDefEq` per step | 9 µs |
| `synthInstance?` per call (cold) | 58 µs |
| `saveState` + `restore`, a million pairs | 42 ns per pair |
| ping round trip (Python driver) | 52 µs |
| `exact? using x, xs` (first call, with the index) | 405 ms, `List.idxOf x xs` |
| `exact?` without `using` | 0 ms, `USize.size` |

## Stage 2: the Haskell driver, and the refactor (done 15:12)

Commits:

- `9aaa7b53` Add a host-agnostic walk of checked programs to cfta-generator
  (`Data.CFTA.Gen.Synthesis.Walk`: `proposals`, `preorder`, the trie of dead
  prefixes, the kept prefix, over a host's `Checker` with `checkerTruncate`
  and `checkerExtend`).
- `794c14d8` Run cfta-ghc's streamed walk on the host-agnostic walk.
  Gate: `hectare-ghc --query Q prelude 60` on 9 Hoogle+ queries (appBoth,
  test, both, mapEither, mapMaybes, map, firstKey, mergeEither, cartProduct),
  old binary against new, gives the same size and result rows (programs,
  skipped, fits, every counter except the times); `ghc-fits-tests` 6/6.
- `76088376` Add lean-oracle (stage 1, without mode (b)).
- `e5e45ce6` Add cfta-lean: the client `Data.CFTA.Lean` and the
  benchmark `hectare-lean`. The intermediate commits `76088376` and
  `e5e45ce6` were cut from the built tree by removing the mode (b) code; they
  were not built on their own.

## Stage 3: the benchmark (final run 15:52)

22 queries over Lean core (`hectare-lean`), one child process and one oracle
per query, `-O2`, the non-threaded RTS. The first 20 have expected programs
that Hectare can propose; `addPairPlus` (`HAdd.hAdd (Prod.fst p) (Prod.snd
p)`) and `mapFunctor` (`Functor.map f o`) have expected programs with no
erased type, so mode (a) cannot find them by design. Libraries: `core`
(71 components with an erased type, 5 skipped: curated List, Option, Prod,
Nat, Bool, and the class methods) and `sweep` (303 components, 124 skipped:
every definition and constructor of List, Option, Nat, Prod, Bool, and
Function, with the same methods).

Mode (a): Hectare proposes, the oracle checks (30 s each).

| Rung | solved | total s of the solved (import) | median s | programs | skipped | round trips | Lean steps | `synthInstance?` (prunes) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| core | 20/22 | 8.12 (2.28) | 0.22 | 71,640 | 69,862 | 1,778 | 4,509 | 986 (767) |
| sweep | 19/22 | 9.61 (2.14) | 0.39 | 7,310 | 5,967 | 1,343 | 3,709 | 860 (276) |

The misses are `addPairPlus` and `mapFunctor` (by design: the first fit is
`Prod.fst p` and `Option.map f o`) and, on the sweep, `firstJust` (size 6): a
timeout after 741,941 programs, of which 734,659 were under a dead prefix and
7,282 went to the oracle (about 1.1 s of round trips). Hectare's enumeration
took the rest of the 31 s.

Mode (b): states from Lean's goals, no Hectare and no erasure (core 25 s,
sweep 15 s each).

| Rung | solved | total s of the solved | median s | states | transitions | build steps | search steps | programs reached |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| core | 22/22 | 18.75 | 0.37 | 13,557 | 14,811 | 1,069,365 | 427,027 | 159,627 |
| sweep | 15/22 | 38.48 | 0.78 | 6,948 | 7,544 | 3,122,833 | 2,673 | 413 |

The deadline of mode (b) is checked between search steps, not while a state
is built, so a run can pass its cap: `firstsOfZip` on the sweep stopped after
27 s of its 15.

On the sweep, mode (b) times out on `addPair`, `maxPair`, `compareLengths`,
`firstJust`, `firstsOfZip`, `maxOrZero`, and `addPairPlus`: each state tries
every one of the 427 leaves with every number of children, so the build steps
dominate (1.2 to 2.4 million on a timeout). An earlier run of mode (b)
without the arguments in the state and without `approxDefEq` (15:34) solved
18/22 on core and 10/22 on the sweep. The "use every argument" rule cuts the
programs that the search reaches: on core, `lookupOr` from 283,760 to 1,
`addPair` from 772,513 to 14,994, and `compareLengths` from 1,623,225 to 58.

Cost per operation in the oracle (warm; `firstJust` on core: 1,316 round
trips, 3,331 steps; `addPairPlus` on the sweep: 6,435 round trips, 11,872
steps):

| Operation | Lean | GHC (cartProduct, prelude, same machine) |
| --- | ---: | ---: |
| unification per step | `isDefEq` 10.4 to 13.6 µs | (in `tcSubTypeSigma`, not timed) |
| constraint call | `synthInstance?` 31 to 39 µs | `simplifyTopWanteds` 71.7 µs |
| complete check | 13 to 20 µs (with `Meta.check`) | (one solver call) |
| snapshot | `saveState` 0.1 µs | freeze and restore 2.9 µs |
| restore | 1.0 µs in the walk; 42 ns per save and restore pair in a loop | (in the freeze figure) |
| one program, Lean side | 59 to 73 µs (1.8 to 2.5 steps) | |
| one round trip, with the Lean side | 122 to 140 µs | (in process) |
| ping round trip | 53 µs (non-threaded RTS), 73 µs (`-threaded`) | |

The GHC figures are from `hectare-ghc --query cartProduct prelude 60` on this
branch: 27,466 programs, 18,704 skipped, 23,280 steps, 10,336 solver calls
(741 ms), 33,616 freezes (97 ms), 7.4 s in all.

Checks per second, mode (a) on core: the oracle checks 12,700 programs per
second (79 µs each on average), or 6,800 with the round trip (148 µs), and
32,000 steps per second (4,509 steps in 1,778 × 79 µs). End to end, with
Hectare's enumeration, the rates are lower and depend on the library: GHC's
`cartProduct` checks 8,762 programs in 7.4 s (1,200 per second), and Lean's
`firstJust` on core 1,316 programs in 4.1 s (320 per second), most of it in
Hectare.

`exact?` (`LibrarySearch.librarySearch` as the tactic calls it) on the first
20 goals: with every argument required (`exact? using`), it closes 17 goals
and gives the expected program for 2 (`sumAll`, `replicateN`), one more up to
eta (`catOptions`: `List.filterMap (fun a => a) xs`), and one that is equal
by definition (`mapOr`: `Option.elim o d f`). Its other answers are other
programs of the type (`List.idxOf x xs`, `List.elem x xs` for `allEqual`,
`List.extract xs n m`) or degenerate ones (`((fun a => d) ∘ fun a => α) xs`,
`Prod.snd p`). It fails on `compareLengths`, `swapAll`, and `containsEither`.
Without `using`, its answers are degenerate (`USize.size`, `Prod.snd p`,
`[]`). The first call takes 330 to 730 ms (it builds the library index); a
warm call takes 0 to 390 ms. `apply?` runs the same `librarySearch` and adds
the partial suggestions with open goals; the benchmark does not count those,
so it compares with `exact?` only.

## Stage 4: the commonalities note (15:57)

`docs/host-checkers.md`: the interface that both hosts implement, mode (a)
and mode (b), the parts that each host gives for mode (b), and what differs
(scopes, constraint solving, snapshots, erasure, process).

Commits after stage 3: `fca0fe43` Search states built from Lean's goals,
without Hectare (mode (b), `approxDefEq` in the step, two new queries);
`9a74985b` the note and this file; a last commit renames a shadowed binding
in `Data.CFTA.Lean` after a cold `-Werror` build in `o0-spike-lean`.

## The cost cascade (16:29)

Asked for after stage 4: report each level's rejections, passes, and time
per decision, and make a cheap host check before an expensive one a
configuration. The oracle's step is now a cascade with counters per level
(arity, an optional head check, `isDefEq`, `synthInstance?` at the step or at
the end, the complete check); `checks head synthEnd` turns the optional ones
on, `configureChecks` in `Data.CFTA.Lean`, and `HECTARE_LEAN_CHECKS` in the
benchmark. Mode (b) also counts its budget prunes and its memo lookups. The
tables are in `docs/host-checkers.md`, "The cost cascade, measured" (run
16:22 to 16:29, all 22 queries, both rungs).

- Mode (a): the head check rejects 0 steps and `isDefEq` 0 (core) or 43
  (sweep), because Hectare's erased types already agree. `synthInstance?`
  rejects 853 of 1,091 calls on core. Hectare costs 39 µs per proposed
  program, the trie and walk 5 to 18 µs per program, the round trip 72 µs.
  `synthEnd` makes it worse: 3,262 round trips instead of 2,586.
- Mode (b): the head check rejects 54% (core) and 65% (sweep) of the steps at
  0.4 µs, against 5.7 µs for `isDefEq`. Core: 22/22 in 15.4 s instead of
  19.5 s. Sweep: still 15/22 (30.6 s instead of 38.5 s for the solved).
- Solved counts are unchanged by the checks in both modes.

## The leaf index in mode (b) (16:45)

`Checks.index` (`checks index`, `HECTARE_LEAN_CHECKS=index`): a new state
looks up its goal type in a `DiscrTree` of the leaves' result types, one tree
for each number of children, and steps only those leaves. The states and
transitions are unchanged (the same counts on core).

- Core: 22/22, 11.9 s for the solved queries with the index (19.5 s without
  any optional level, 15.4 s with the head check), 193,827 refine calls
  instead of 1,069,365; the decide calls are the same 75,659.
- Sweep (15 s each): 17/22 with the index and the head check, against 15/22
  with the head check alone; `firstsOfZip` and `maxOrZero` are new.
  `firstJust` took 31 s against its 15 s cap (the deadline is checked between
  search steps).
- The index skips 82% of the leaf and arity pairs at 15 to 35 ns each; after
  it, the head check rejects nothing.

## The `hectare?` tactic (19:23)

`Oracle/Tactic.lean` (syntax, options) and `Oracle/Suggest.lean` (the search):
a tactic in pure Lean, on mode (b) with the leaf index, that proposes
programs for the goal from its locals and from the namespaces of its types
(and of the types that their constants return), smallest first, closes the
goal with the first, and reports `Try this` suggestions. Options: `size`,
`suggestions`, `useAll`, `seconds`. `OracleTest/Tactic.lean`: nine
`#guard_msgs` tests (classes `BEq`, `Add`, `Zero`, `Max`; `Functor.map` on
`Option`; `x >>= f` over a monad variable; `useAll := false`; no program).
The oracle's `suggest` request and `hectare-lean --suggest` compare it with
`exact? using` on the 22 queries (30 s each):

- `hectare?` finds the intended program for 16 of 22: first for 6, in the
  first 5 for 10; median 0.4 s. It does not reach `maxPair`,
  `compareLengths`, `firstJust`, `firstsOfZip`, `addPairPlus`, and
  `maxOrZero`, with 315 to 1,544 leaves.
- `exact? using` gives the intended program for 2 (`sumAll`, `replicateN`).

The search stops after `seconds`, or at nine tenths of `maxHeartbeats`: a
search's heartbeats count against the elaboration around the tactic, so the
tactic leaves it the rest. The `lookupOr` test needs `set_option
maxHeartbeats 0` and 30 s. The `--suggest` comparison ran at 18:50, before
that rule; the oracle sets `maxHeartbeats` to 0, so the rule does not change
it. All nine `#guard_msgs` tests pass (19:23).

Two changes to the search over states came with it: the arguments to use go
to the earliest children first (`f x y` before `f y x`), and a state that the
deadline stops is not kept. Mode (b) on core with the index is still 22/22
in 0.17 to 3.2 s a query; a few programs-before-the-expected counts change
(`compareLengths` 58 to 49, `takeDrop` 2 to 4, `containsEither` 12 to 11).
The cascade tables in `docs/host-checkers.md` are from `1114da08`, before
these changes.

## Rebase onto the merged walk (19:36)

`spike/lean-oracle` is rebased onto `origin/feature/microcfta-ghc`
`78655654` (#125 and #126 merged); the spike's own copies of the walk and of
the GHC port are gone, and `Data.CFTA.Lean.streamFits` gives the merged walk
`Limits` and `Hooks` (commit "Run cfta-lean on the merged host-agnostic
walk"). Gate: mode (a) 20/22 on core and 19/22 on the sweep (30 s), mode (b)
with the index 22/22 on core (25 s) and 17/22 on the sweep (15 s, index and
head check), the same as before the rebase; the nine `#guard_msgs` tests
pass; `-Werror` passes. The worktrees `host-walk` and `host-walk-base` are
removed.

## When each mode wins (19:45)

The `features` request reads three features of a query before the search
(a higher-kinded variable, a class over a type constructor, child goals that
stay open), with the names that the GHC side uses. At 30 s a query, mode (a)
solves 20 and 19 of 22 (core, sweep), and mode (b) with the index 22 and 20.
Only mode (b) solves `addPairPlus` (core) and `mapFunctor` (both); mode (a)
solves nothing that mode (b) misses, and it is about 27 times faster on
`addPair`, `maxPair`, and `compareLengths` on the sweep. The features fire
on many queries that mode (a) solves fast, so a classifier on them does not
beat the portfolio "(a) for 2 s, then (b)", which solves the union (22 and
20) within 40% (core) and 4% (sweep) of the time of an oracle that knows the
faster mode. `docs/host-checkers.md`, "When each mode wins", has the tables.

## The portfolio (20:21)

`hectare-lean --portfolio` and `hectare?` (now its default, `budget := 2`):
mode (a) for the budget, then, when it exhausted its bound or ran out of
time, the search over states for the rest. In the tactic, mode (a) comes from
the new program `hectare-propose` (the walk of `Data.CFTA.Lean` with the
tactic as its checker on its standard input and output), named by
`HECTARE_PROPOSER`; without it, only the search over states runs.

- Benchmark, 30 s a query: core 22/22 in 12.7 s (19 by mode (a), 3 by mode
  (b)), sweep 20/22 in 10.2 s (19 and 1): the union of the two modes, at the
  time of knowing the faster mode on the sweep (10.3 s) and 34% over it on
  core (9.5 s).
- Tactic against `exact?` on the 22 queries: the intended program for 19
  (first for 6, in the first five for 11), against 16 for the search over
  states alone and 2 for `exact? using`; median 0.26 s to the intended
  program. The first program is the same as with the search over states
  alone for 16 queries; where it changes, neither run's first program is
  the intended one.
- The tactic's tests: ten `#guard_msgs` tests pass with the proposer; the
  higher-kinded test now has two versions, the portfolio (mode (a)'s
  `#[Option.map f o].back!` comes second) and `budget := 0` (`f <$> o`).

## Design note: a host-agnostic portfolio and mode (b) (20:43)

`docs/host-agnostic-modes.md`, no code. The portfolio (an outcome for each
run, a schedule of proposers with budgets, fits each once, one checker) fits
in a module next to the walk. Mode (b)'s budget, key, table, splits, and
search are the same in Lean and GHC and can move to `cfta-generator`;
the host gives key, open (Lean only), candidates, refine (which decides what
it can), complete, and snapshot. With the GHC prototype's Generalize, mode (b) is a
proposer whose programs the walk's `Checker` checks, so it also works across
Lean's pipe (one round trip a state and a program); Unfold needs the host at
every search step (28 s of round trips on core). Degenerate fits: the
decision is the host's (a fresh rigid leaf; Lean also definitional
equality, which shows `#[o].back! = o` by `rfl`), the ranking is
host-agnostic, and the parametricity check can be generic over the
`Checker` given the host's rigid leaf. The earlier remark that mode (b) ran
in a warm oracle in the portfolio was wrong: mode (b) alone takes 9 ms on
`mapFunctor` in the oracle too; the portfolio pays the oracle's start once.

## Host-agnostic modes, steps 1 and 2 (2026-10-15 06:22)

On `spike/host-agnostic-modes`. Step 1: the walk's outcome and
`Data.CFTA.Gen.Synthesis.Portfolio`; GHC's ladder and Lean's rows did not
change. Step 2: mode (b) in `cfta-generator`
(`Data.CFTA.Gen.Synthesis.States`), with GHC's goals
(`Data.CFTA.GHC.States`, ported from `feature/ghc-mode-b`) and Lean's
(the oracle's requests `goals` and `transitions`). Measurements in
`docs/host-agnostic-modes.md`, "As built":
- GHC mode (b): 24 and 34 solved, as the GHC prototype's search, in 14% and 42% less
  time; the portfolio "(a) for 60 s, then (b)": 25 and 37, the union.
- Lean generic mode (b): 22 and 18 (the oracle's own search: 22 and 17),
  2.9 times slower on core and 17% faster on the sweep. One `extend` round
  trip for each complete program is its cost, and 0.48 refinement round
  trips a state. The portfolio: 22 and 20, as the oracle's own.
- Two traps on the way: the transitions must keep the host's order (GHC's
  index puts the leaves of an exact head first), and the refinements of a
  goal must share one walker (a walker's variables come from the types of
  every leaf: 26 µs a freeze instead of 0.4 µs).
- Follow-up: a heap guard in the portfolio. On GHC, `takeNdropM` runs out
  of memory in Hectare's automaton of size 7 in mode (a) (about 33 s on
  rung 1 and 45 s on rung 2, before its 60 s budget), so the whole query
  dies and mode (b) does not get its turn. A run that stops near a heap
  limit, with an outcome of its own, would let the next mode run.

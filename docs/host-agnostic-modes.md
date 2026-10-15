# A host-agnostic portfolio and mode (b)

A design note, without code. `docs/host-checkers.md` names the two modes and
the interface of a host checker; the Lean spike measured that a portfolio of
the two modes ("mode (a) for 2 s, then mode (b)") solves the union of both
modes at near the cost of knowing the faster mode in advance. This note says
what `cfta-generator` would need so that one portfolio and one mode (b)
serve both hosts, compares the two mode (b) prototypes (Lean:
`cfta-lean/oracle/Oracle/States.lean`; GHC: `Data.CFTA.GHC.States` on
`feature/ghc-mode-b`), and says where the check for degenerate fits belongs.
Steps 1 and 3 of the list at the end are now built; "As built" at the end
says what changed from this design and what they measured.

## What is host-agnostic today

`Data.CFTA.Gen.Synthesis.Walk` (#126) has mode (a) without a host:
Hectare's automaton of each size over the erased leaves (built, reduced, and
listed, each part timed), the preorder tokens, the prefix that the host
holds, the trie of dead prefixes, the fits each once, and `Limits` (size,
programs, deadline). The host gives a `Checker` (`checkerTruncate`,
`checkerExtend`), and GHC (in `TcM`) and Lean (over a pipe) both use it.

## The portfolio

### What it needs

- **An outcome for each run.** A run ends in one of three ways, and the
  next run depends on which:
  - *solved*: the caller's function stopped it (the expected program, or
    enough fits);
  - *exhausted*: it looked at every program up to the size;
  - *out of time*: it reached its deadline.

  The walk has the third (`progressOutOfTime`) but not the first two apart:
  the caller knows when its function said stop. The walk should return the
  outcome itself, for example as a field `progressOutcome` of `Progress`.
- **A proposer type.** A run is a proposer with a budget: Hectare through the
  walk (mode a), or the table of states (mode b). Both take `Limits` and a
  function on fits, and both give `Progress` with an outcome, so a proposer
  is one function of that shape.
- **A schedule.** The portfolio is a list of proposers, each with a budget,
  and one deadline for all of them. It runs the first with
  `min budget (deadline - now)`; on *solved* it stops; on *exhausted* or
  *out of time* it runs the next with the rest of the time. The budget lives
  in `Limits` (`limitDeadline` of each run); the outcomes live in the
  `Progress` of each run, and the portfolio's result keeps them all.
- **Fits each once, across runs.** A fit is a `Program`, so the set of
  reported programs (by their preorder tokens, as the walk keeps now) can
  move from the walk to the portfolio, so that mode (b) does not report a
  program again that mode (a) reported.
- **One checker for all runs.** Both proposers check with the host's
  `Checker` (see below for mode (b)), so the host's start (Lean's import of
  `Init` and the erasure of the library) and its caches (GHC's table of
  verdicts) serve every run. In the Lean benchmark the portfolio pays the
  oracle's start once: on `mapFunctor` (sweep) mode (a) exhausts its bound in
  0.36 s with the start, and mode (b) then needs 0.07 s, so the query takes
  0.43 s, against 0.41 s for mode (b) alone.

The schedule, the outcomes, the deduplication, and the ranking (below) need
no host types, so they fit in a module next to the walk, for example
`Data.CFTA.Gen.Synthesis.Portfolio`. The budget (2 s) is the caller's.

### What the hosts measured

| | Lean, core (30 s) | Lean, sweep (30 s) | GHC, rung 2 (120 s) |
| --- | ---: | ---: | ---: |
| mode (a) alone | 20 | 19 | 36 |
| mode (b) alone | 22 | 20 | 34 |
| the portfolio | 22 | 20 | 37 |

The GHC figures are the GHC prototype's (`feature/ghc-mode-b`, with its two fast
checks; the portfolio's count is from the union of the two modes' solved
sets). In both hosts the portfolio solves the union.

## Mode (b) in `cfta-generator`

### The parts without a host

Both prototypes have the same algorithm, so these parts can move to the
generic code unchanged:

- **The budget of a goal**: its size, and the query arguments that its
  program must still use. A state with more arguments to use than its size
  is empty.
- **The key of a state**: the host's key of the goal type, the size, and the
  sorted arguments to use.
- **The table** from keys to transitions, built on the first visit: a
  transition is a leaf, its number of children, and the splits of the rest
  of the budget over the children (the compositions of the size, times the
  assignments of the arguments, without a child that must use more
  arguments than its size) whose children's states are not empty.
- **The search** in preorder, size by size, with a budget for each goal, and
  the deadline checked in the builds and in the search.
- **The figures**: states, transitions, build steps, the splits that the
  budget and the empty children reject, the memo's lookups and hits, and the
  leaves that the index skips (the cascade of `docs/host-checkers.md`).

### The host's operations

| Operation | What it does | GHC (`States.hs`) | Lean (`States.lean`) |
| --- | --- | --- | --- |
| **key** | a goal type up to the renaming of its unification variables | `stateKey`: zonk, number the unification variables in order, with level and kind | `instantiateMVars`, then `abstractMVars` (also the universe level metavariables) |
| **open** | a goal of a key, for the build | not needed: the build steps on the goal itself, between a freeze and a restore | `openAbstractMVarsResult`: a fresh goal |
| **candidates** | the leaves (with a number of children) whose result can fit a goal | a map from the result head after `k` arguments (a type constructor, the arrow, a rigid variable; a bound variable matches all) | a `DiscrTree` of the result types after `k` arguments, `getUnify` |
| **refine** | a leaf with `k` children on a goal: the child goals, or a failure | `step`: `tcSubTypeSigma`, the fast checks, the solver under the hole's givens | `step`: binder instantiation, `isDefEq` (with `approxDefEq`), `synthInstance?` on the ground instance problems |
| **decide** | the residual constraints, once their types are known | the solver on the walker's wanteds; open ones stay as guards | `synthInstance?` on the pending problems without metavariables; open ones stay pending |
| **complete** | a complete program fits | `complete`: every wanted solved | no pending problem, no metavariable, `Meta.check` |
| **snapshot**, **restore** | undo a step | `freeze`, `restore` (2.9 µs) | `saveState`, `restore` (0.1 and 1.0 µs) |
| **walker key** (optional) | the key of a whole walker, for a table of verdicts | `stateKey` of the walker with its wanteds | not used |
| **sharing** (later) | the unification variables that sibling goals share, as positions | not used | not used |

The decide operation is inside refine and complete in both hosts: a step
decides what it can, and keeps the rest in the host's walker. So the generic
code sees a walker as an opaque value with its open goals, and needs
neither the constraints nor the decide operation by itself.

Neither prototype encodes the sharing yet. A child's state is built without
its siblings' unifications, so the table over-approximates, and the search
ties the siblings by stepping each transition again on the real walker. The
sharing operation is needed only to read the table as an ECTA with equality
constraints (for counts, ranks, and sampling).

### Two ways to tie the siblings, and the process boundary

- **Unfold** (Lean's only way, GHC's option): at each goal of the search,
  the state is the one of the real goal, with the earlier siblings'
  unifications. The search needs the key of the real goal at every step.
- **Generalize** (GHC's option): the search takes the child's state that
  the build recorded, and the real step checks it again. The table then
  gives a stream of candidate programs without the real goals, and the real
  steps are exactly what the walk's `Checker` does.

With Generalize, mode (b) is a proposer like Hectare: the table makes the
programs, and the generic walk checks them with the host's `Checker`, with
the trie of dead prefixes and the shared prefix. That works across a process
boundary with two coarse requests: "build the state of a key" (one round
trip a state) and the walk's `extend` (one round trip a program). Unfold
needs the host at every step of the search.

For Lean over a pipe (66 µs a round trip, `docs/host-checkers.md`):

| | core | sweep |
| --- | ---: | ---: |
| states (one build request each) | 13,531: 0.9 s of round trips | 65,426: 4.3 s |
| search steps (one request each, for Unfold) | 426,938: 28 s | 5,579,383: 368 s |
| the search over states in-process now | 11.4 s | 105 s |

So a generic mode (b) serves GHC in process with either way, and Lean only
with Generalize and the coarse requests; the Lean tactic, which runs in Lean,
keeps its own copy of the algorithm. The GHC prototype measured that Generalize builds
half of Unfold's states, solves the same queries, and is 9 to 17% faster in
GHC, so Generalize is the better default for the generic code too. The Lean
prototype has not tried it.

## Lean's mode (b) against GHC's

The same:

- the key (a goal type up to renaming, the size, the arguments to use), the
  budget and its splits, the table built once, the emptiness of a state;
- an index of the leaves by their result type after `k` arguments;
- the search in preorder that steps each transition again on the real
  walker, which ties the siblings and decides the residual constraints when
  their types are known;
- Hectare's rule that every query argument occurs at least once;
- the deadline in the builds and in the search.

Different:

| | GHC | Lean |
| --- | --- | --- |
| build | on the goal itself, with freeze and restore | on a fresh goal opened from the key |
| children's states | Unfold or Generalize | Unfold |
| index | the result head only, with a cap on `k` for a concrete result | the whole `DiscrTree` key path (heads and arguments), with no cap |
| a result of any type (`undefined`, `mempty`) | left out, as in mode (a) | kept: `HAdd.hAdd` fits through its out-parameter, so `addPairPlus` is solved, at the cost of bare-metavariable children |
| Hectare's rule for `[]` | applied to every first argument | not applied |
| table of verdicts in the search | by the real walker's key and the token (521 s of keys on rung 1) | none |
| what it finds that mode (a) cannot | `headLast` (rung 2); the higher-kinded queries without hand specializations | `addPairPlus` and `mapFunctor` (no erased type) |
| where it loses to mode (a) | `cartProduct`, `applyNtimes`, `firstJust` (timeouts at sizes 5 and 6) | `addPair`, `maxPair`, `compareLengths` on the sweep (26 to 28 times slower) |
| fits | `fitIgnoresPart` always `False` | no check |

## Degenerate fits

Two kinds of degenerate fits come out of the searches:

- **A fit that ignores a part**, as `const xs n`: it still fits when an
  argument subterm has a fresh rigid type, so by parametricity it cannot use
  that subterm. `cfta-ghc` checks this exactly (`fitIgnoresPart`) and
  ranks such fits last.
- **A fit that equals a smaller fit**, as `#[Option.map f o].back!` from the
  Lean portfolio's mode (a): it uses every part, so the parametricity check
  does not flag it (`#[x].back!` with `x` of a fresh type does not have the
  goal's type), but it is the smaller fit `Option.map f o` in a wrapper.
  Lean's definitional equality decides it: `#[o].back! = o` and
  `(Array.singleton o).back! = o` hold by `rfl` (checked with Lean 4.35.0 on
  2026-10-14). It does not decide an equality that needs induction:
  `(List.reverse xs).length = xs.length` is not `rfl`.

Where each part belongs:

- **The decision is the host's.** It needs the host's types: a value of a
  fresh rigid type for the first kind, and definitional equality for the
  second. GHC has the first (`rigidLeaf`) but no definitional equality of
  terms; Lean has both.
- **The ranking is host-agnostic.** A fit with a flag goes after the fits
  without one, in a stable order, across every run of the portfolio. That is
  what `synthesizeFits` does for GHC now, and it needs no host types.
- **The first check can be generic too**, given one host leaf. The
  replacements of a program's argument subterms by a leaf (`replacements`
  in `Fits.hs`) work on `Program`, and "does the replaced program fit" is a
  `checkerTruncate 0` and a `checkerExtend` with the host's rigid leaf as
  the replacement. So the host needs only to give a leaf of a fresh rigid
  type in its checker (GHC: `rigidLeaf`, in the checker's leaves under the
  name `_` since #125), and the generic code runs the check. Then it
  applies to mode (b)'s fits as well; the GHC prototype's mode (b) sets the flag to
  `False` now.
- **The second check stays a host operation**: `checkerSame :: Program ->
  Program -> m Bool` (whether two complete programs are equal), optional,
  with no GHC instance.

What Lean needs for them:

- for the first check, a local `x : β` of a fresh local type `β : Type` in
  the goal's context (in the oracle's telescope and in the tactic's context),
  as a leaf of the checker; the cost is one `extend` for each argument
  subterm of each fit;
- for the second, `isDefEq` of the two terms at the default transparency,
  under a heartbeat bound, against the earlier and smaller fits of the same
  goal; the cost is one `isDefEq` for each pair, so it is for the few fits
  that a tactic shows.

## Steps, in order

1. The outcome in the walk's `Progress`, and the portfolio module with the
   schedule, the deduplication, and the ranking by flags.
2. The parametricity check as generic code over the `Checker`, with the
   host's rigid leaf; the GHC checker gives it as now.
3. Mode (b) in `cfta-generator`: the table, the budget, the splits, the
   search, with Generalize as the default and the host operations key,
   candidates, refine, complete, and snapshot; GHC's `States.hs` becomes
   its instance, and the Lean oracle gets the coarse "build the state of a
   key" request.
4. The sharing as equality constraints, to read the table as an ECTA.

## As built

`spike/host-agnostic-modes` has step 1 (the outcome and the portfolio) and
step 3 (mode (b) in `cfta-generator`), on `origin/microcfta` `7bfb69d1`.

### What changed from the design

- **One host operation for the table.** `goalsTransitions` (in `Goals`)
  gives, for the key of a goal and numbers of children, each leaf whose step
  passes, with the keys of the child goals and its place in the host's
  order (`Refinement`). It holds the key, open, candidates, and refine
  operations of the table above. Complete and snapshot are the walk's
  `Checker`, which checks the programs of the search. So a host gives a
  `Goals` value and the `Checker` that mode (a) already has.
- **The refinements by key and number of children.** The host refines a
  goal once for all sizes: a new size asks only for the new number of
  children. The host's order (in GHC, the leaves of an exact head before
  those of a variable result) does not depend on the numbers asked, so the
  merged refinements keep it. A first version sorted them by leaf. GHC then
  reached up to 2,000 times more programs before the expected one
  (`appBoth`: 29,245 against 13) and solved 22 queries on rung 1, not 24.
- **Generalize only.** The search walks the table depth first and gives
  each complete program to the `Checker`, from the prefix that it shares
  with the last one. A death at token `i` ends the splits of the transition
  at `i`, and the walk's trie of dead prefixes (now exported) skips the same
  prefix under other splits. The host holds no frame while it refines the
  goals of a size.
- **The emptiness of a split** stops at its first empty child.

### GHC

`Data.CFTA.GHC.States.holeGoals` is ported from `feature/ghc-mode-b`
(`492f9d6a`): the key, the step on a walker of the goal between a freeze
and a restore, the index by result head, and the rule for a result of any
type. The table, the splits, and the search are the generic ones. The real
steps are those of the walk's checker, with its table of verdicts and the
fast rejects of #128, so the fits of mode (b) get the check of
`fitIgnoresPart` too. `optionModes` runs the modes as a portfolio, with mode
(a) alone by default, so `synthesizeFits` does not change. Not ported:
Unfold, `ghc-fits --states`, and the figures of the index.

The refinements of a goal step on one walker: the variables of a walker
come from the types of every leaf, and a walker for each leaf made a freeze
cost 26 µs, not 0.4 µs. Alone and pinned, `indexesOf` (rung 2) took 85.9 s
so, against 15.4 s with one walker and 50.5 s with the GHC prototype's binary, whose
build gets the same sharing from GHC's floating of the walker out of the
loop.

### Lean

The oracle has two new requests: `goals` (the leaves of the protocol, the
key of the goal, and the index) and `transitions` (the refinements of a
goal, in one round trip). The constants without a Hectare type get indices
after the arguments, so `extend` checks the programs of both modes. The
oracle's own search over states (Unfold, `--states`) and the tactic's
portfolio stay as they are.

### Measurements

GHC, the Hoogle+ ladder (`hectare-ghc RUNG 120 1400M 8`, -O2, the children
pinned as in the GHC prototype's runs; s: the seconds of the solved queries, and all:
the seconds of the 45 queries):

| | rung 1 solved | s | all | rung 2 solved | s | all |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| mode (a) | 25 | 29.8 | 687 | 36 | 90.6 | 884 |
| mode (b), the GHC prototype's own search (`final-b`) | 24 | 183.3 | 1,388 | 34 | 168.8 | 1,482 |
| mode (b), generic | 24 | 157.7 | 1,432 | 34 | 98.2 | 1,419 |
| portfolio: (a) for 60 s, then (b) | 25 | 29.0 | 1,115 | 37 | 176.0 | 1,061 |

- **Mode (b)** solves the same queries as the GHC prototype's search on both rungs,
  in 14% and 42% less time on them, with a quarter to three quarters of the
  solver calls: the walk's checker keeps the verdicts of its steps.
- **The portfolio** solves the union of the two modes on both rungs (25 and
  37), as the GHC prototype's simulation of the same schedule did. On rung 2 mode (b)
  adds `headLast` after mode (a)'s 60 s (83 s in all); mode (a) alone solves
  `applyNtimes`, `cartProduct`, and `firstJust`. Mode (b) takes 67% of the
  portfolio's time on rung 1 and 53% on rung 2. All of it is on queries that
  neither mode solves, except the 23 s that solve `headLast`. `takeNdropM` runs out of memory in Hectare's
  automaton of size 7 in mode (a), as in the GHC prototype's runs, so mode (b) does not
  get its turn there.
- **The fits of mode (b)** get `fitIgnoresPart`: the expected program of
  `indexesOf` (rung 2) is the 268th fit, and the first of those that use
  every part of themselves.

Lean, the 22 queries of each rung with the time limits of step 1 (s: the
seconds of the solved queries):

| | core solved | core s | sweep solved | sweep s |
| --- | ---: | ---: | ---: | ---: |
| mode (a) | 20 | 8.4 | 19 | 9.8 |
| mode (b), the oracle's own (Unfold, in Lean) | 22 | 13.0 | 17 | 36.6 |
| mode (b), generic (Generalize, over the pipe) | 22 | 37.6 | 18 | 36.1 |
| portfolio, the oracle's own: (a) for 2 s, then (b) | 22 | 13.5 | 20 | 11.2 |
| portfolio, generic: (a) for 2 s, then (b) | 22 | 35.2 | 20 | 10.3 |
| portfolio, generic: (a) for 15 s, then (b) | 22 | 30.6 | 20 | 10.4 |

- **Round trips.** The refinements take 0.48 round trips a state (5,242
  for 10,918 states on core, 13,384 for 27,944 on the sweep). The time goes
  to the checks: one `extend` for each complete program (282,852 on core,
  549,186 on the sweep), about 105 µs each. Generalize reaches more
  complete programs than the oracle's Unfold (`addPairPlus`: 186,020
  against 95,240), because the state of a child does not see the
  unifications of its siblings and the check comes after the whole
  program. So over a pipe the cost of Generalize is in its programs, not in
  its states: the 28 s that the table above gives for the search steps of
  Unfold on core are now 28 s of program checks.
- **Generic against the oracle's own.** The generic mode (b) also solves
  `compareLengths` on the sweep (the oracle's own times out at 15 s), and it
  is 17% faster on the 17 queries that both solve there (30.5 against
  36.6 s), but 2.9 times slower on core.
- **Share of time.** With 2 s for mode (a), the generic portfolio spends
  87% of its time in mode (b) on core and 89% on the sweep, and mode (a)
  solves 19 of the 22 on core and 19 of the 20 on the sweep. With 15 s for
  mode (a), mode (b) takes 78% and 48%.
- **Next for a host over a pipe:** one round trip for several programs, as
  for all the leaves of the last open goal of a prefix.


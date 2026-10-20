# Host checkers: one design for GHC and Lean

Historical notes from the previous spike. See [the Kimina restart](lean-spike.md) for the current scope.

A typed-hole synthesizer needs programs that a real typechecker accepts.
Hectare's automaton enumerates programs well, but it knows only erased,
first-order types. A host's typechecker (GHC's `TcM`, Lean's `MetaM`) knows
the real types, but it cannot enumerate. `cfta-ghc` combines them for
GHC, and the Lean spike (`cfta-lean`) does the same for Lean. This note
names the parts that the two hosts share, the parts that differ, and the
interface for a second mode in which the host builds the automaton from its
own goals.

## The two modes

- **Mode (a), Hectare proposes, the host checks.** Hectare lists programs
  over the erased types of the leaves, size by size. The host checks each
  program in preorder, prefix by prefix, and a trie of dead prefixes skips
  every later program under a failing prefix. This is `cfta-ghc` and
  the Lean spike's `hectare-lean`.
- **Mode (b), the host builds states from its goals.** A state is a goal (its
  type with the unification variables instantiated, up to their renaming) and
  a size. A transition is a leaf whose refinement step succeeds on the goal;
  its children are the states of the step's child goals. The states are
  memoized, so each subgoal is solved once for all the programs that reach it.
  Sibling goals that share a unification variable become equality constraints
  between the children's paths, and the instance problems that stay open
  become guards on the transition. The Lean spike has a prototype
  (`Oracle/States.lean`, `hectare-lean --states`); the GHC prototype builds the GHC
  version.

## The interface

### What every host gives

A host has these types. The names are the Lean spike's; the GHC names are in
parentheses.

| Part | GHC | Lean |
| --- | --- | --- |
| **Goal**: an open hole with a type | a type with unification variables, under the hole's implications | an expression metavariable (`MVarId`) in the query's local context |
| **Leaf**: a component or a local of the query | `Leaf` (name, type, can head) | `Leaf.const` (instantiated with `mkConstWithFreshMVarLevels`) or `Leaf.fvar` |
| **Walker**: the open goals, leftmost first, and the residual constraints | `Walker` (variables, wanteds, goals) | `Walker` (goals, pending instance problems) |
| **Snapshot**: the state before a step | `Frozen`: the contents of every reachable unification variable | `Meta.SavedState`: a pointer to the persistent metavariable context |

and these operations:

- **erase** a leaf's type and the goal type to Hectare's first-order type, or
  give none ("Data.CFTA.GHC.Erase", `Oracle/Erase.lean`);
- **step** a walker: give its leftmost goal a leaf with `k` children, as a
  refinement fit against `α1 -> ... -> αk -> goal`, with fresh unification
  variables for the children, which become the new goals. The step fails when
  the leaf does not fit or a residual constraint cannot be solved any more;
- **complete** a walker: no open goal, every residual constraint solved, and
  (Lean) `Meta.check` on the instantiated term;
- **snapshot** and **restore**, because a step writes unification variables
  and does not undo itself.

### Mode (a): the checker

The walk of `Data.CFTA.Gen.Synthesis.Walk` (in `cfta-generator`, with no
host dependency) sees a host only through a `Checker`:

```haskell
data Checker m = Checker
    { checkerTruncate :: Int -> m ()          -- keep this many frames
    , checkerExtend :: [Token] -> m Extension -- step these tokens, then complete
    }
data Extension = Died Int | Done Bool
type Token = (Text, Int)                      -- a leaf and its number of children
```

The host keeps a stack of frames, one for each checked token of the current
prefix: frame `i` holds the snapshot from before step `i` and the walker after
it. `checkerTruncate k` restores the snapshot of frame `k` (the first frame
that goes) and drops it and the later frames. `checkerExtend` pushes one
frame per token; on a failure at index `n` it restores that step's snapshot
and answers `Died n`, and after the last token it answers `Done` with the
complete check. The walk owns everything else:

- `proposals`: Hectare's programs over the erased leaves (components,
  argument-only components, and the query's required arguments), size by
  size, with each group representative expanded;
- the preorder tokens of each program, the longest prefix that it shares
  with the host's frames, and the trie of dead prefixes;
- the counts (programs, skipped, fits, size), the hooks after each size and
  before each program, and the stop when the caller's function says so.

The seam is at "truncate and extend", not at "step", for two reasons. The
GHC instance keeps its frames, `Frozen`, `Walker`, and `Leaf` inside
`cfta-ghc`, so the port changes no behaviour (the size rows of nine
Hoogle+ queries are identical before and after). And a host in another
process answers a whole program in one round trip, instead of one round trip
for each step.

### Mode (b): states from goals

For states, a host gives four more operations:

- **key**: a goal type with its unification variables instantiated and
  renamed canonically, so that two goals that differ only in their variables'
  names share a state. GHC: zonk, then rename the metavariables in order of
  occurrence. Lean: `instantiateMVars`, then `abstractMVars`, which also
  abstracts the universe level metavariables; `openAbstractMVarsResult` opens a
  key as a fresh goal.
- **refine**: a fresh goal of a key, a leaf, and `k`: the child goals and the
  residual constraints, or nothing. This is the step of mode (a) on a fresh
  walker.
- **sharing**: which unification variables the child goals share with each
  other and with the parent goal, as positions in their types. These become
  the ECTA equality constraints between the children's paths.
- **decide** a residual constraint once its types are known: solved, failed,
  or still open. GHC: the solver on the wanteds without unification variables.
  Lean: `synthInstance?` on an instance problem without metavariables outside
  its out-parameters.

The part without a host is the table of states by key and size, the splits of
a size over the children, the emptiness of a state (a state is empty when no
transition has a split whose children are all non-empty), and the reading of
the table as an automaton: a node per state, an edge per transition and
split, and the sharing as equality constraints. The automaton then has
Hectare's enumeration, counts, ranks, and sampling, and the checker of mode
(a) can check its programs. The two modes thus compose: mode (b) replaces
Hectare as the proposer, and the checker stays.

The Lean prototype keeps the table in Lean and does not build the ECTA yet.
It ties the sharing differently: its search walks the table in preorder and
steps each transition again on the real goal, so that the earlier children's
assignments reach the later children before their states are looked up. The
open instance problems stay pending in the walker, and each later step
decides the ones whose types it fixed.

### The cost cascade

Both modes are cascades of decisions: each level rejects some candidates and
passes the rest to the next, more expensive level. The hybrid that we expect
to keep puts each pruning at the level where it is cheap. So the interface
orders the levels from cheap to expensive, and it makes the optional ones a
configuration:

| Level | Where | Decides | Configured by |
| --- | --- | --- | --- |
| 1. Hectare over erased types | the walk's proposer | which programs exist at all | the proposer: `proposals` (mode a) or the table of states (mode b) |
| 2. structural filters | erasure, Hectare's pruning rules, the host's arity check, the arguments still to use (mode b) | leaves and shapes that cannot fit | the erasure, `optionAvoid`, the state's budget |
| 3. dead prefixes | the walk (`Dead` trie) | programs under a prefix that failed | always on |
| 4. head check | the host's step, before unification | leaves whose result type has another rigid head than the goal | Lean: `Checks.head` (`checks head`); GHC: `checkInsoluble`, always on |
| 5. unification | the host's step | leaves whose type does not fit the goal | always on: it is the step |
| 6. constraint solving | the host's step, or the complete program | residual constraints without an instance | Lean: `Checks.synthAtEnd` (`checks synthEnd`); GHC: the skip rule decides when the solver runs |
| 7. the goal memo | mode (b): the table of states | goals whose state is empty, for every program that reaches them | the key and the budget |
| index of the leaves | mode (b): a new state, before its steps | leaves whose result type cannot match the goal's | Lean: `Checks.index` (`checks index`), a `DiscrTree` for each number of children |

A level is a pure decision with counters: its rejections, its passes, and its
time. A host's step runs its levels in order, and the first rejection ends
the step, so a new cheap level (an index of the leaves by result head, a
check of argument heads) goes in front of the expensive ones without a change
to the walk or to the other levels. The Lean oracle reports every level in
its `stats` reply, and `hectare-lean` prints them as `cascade` rows.

## What differs between the hosts

**Scopes: levels and implications against local contexts and depth.** GHC's
givens and skolems live in the hole's implications, and a step runs at the
level of the innermost implication so that the hole's own unification
variables are touchable; every solver call rebuilds the implications around
the wanteds. Lean's givens are local instances of the local context
(`forallTelescope` registers `[BEq α]`), the type parameters are free
variables (rigid by construction), and the metavariables of the walk are at
the current metavariable-context depth, so they are assignable and the free
variables are not. Nothing has to be rebuilt per call.

**Constraint solving: one solver over all wanteds against one problem at a
time.** GHC solves the wanteds of the whole program so far with
`simplifyTopWanteds`, and undoes the solver's own unifications and defaulting
after each call. Lean's instance problems are independent: `synthInstance?`
runs at a deeper metavariable-context depth, so it cannot assign the walk's
metavariables (except out-parameters), and a solved problem stays solved. So
the Lean step synthesizes each problem once, when its type becomes ground,
and keeps the others pending. GHC's "solver skip" (no new equality, every
wanted still open) corresponds to Lean's "every pending problem still has a
metavariable".

**Snapshots.** GHC's unification variables are mutable references, and the
zonker writes back into filled ones, so a freeze must walk every reachable
variable, also through filled ones, and a restore writes them all back. Lean's
metavariable context is a persistent map: `saveState` keeps a pointer, and a
restore writes it back.

**Erasure of dependent types.** GHC's types are nearly first order after the
class contexts go. Lean's erasure drops instance-implicit binders, drops
value indices of type constructors (`Fin n` becomes `Fin`, an
over-approximation), and leaves out explicit type arguments, proof
arguments (`List.head : (as : List α) → as ≠ [] → α`), propositions, and
type formers. Out-parameter classes lose most: `HAdd.hAdd : α → β → γ`
erases to a result of any type and is left out, so `+` reaches Hectare only
through `Add.add`.

**Process.** The GHC walk runs inside `TcM`, in the same process as Hectare.
The Lean walk runs in a child process; each program costs one round trip of
the line protocol.

## Measurements

From the Lean spike (`STATUS-lean.md` has the full tables): 22 queries over
Lean core, `-O2`, one oracle per query. Two of them (`addPairPlus` with `+`,
`mapFunctor` with `Functor.map`) have expected programs without an erased
type. The libraries are `core` (76 constants) and `sweep` (427: every
definition and constructor of six namespaces).

| | mode (a), core | mode (a), sweep | mode (b), core | mode (b), sweep |
| --- | ---: | ---: | ---: | ---: |
| solved (30 s; mode (b) with the leaf index) | 20/22 | 19/22 | 22/22 | 20/22 |
| median s of a solved query | 0.22 | 0.42 | 0.28 | 1.03 |
| host steps | 7,458 | 46,901 | 620,310 | 10,417,832 |

These are the runs of 19:32 to 19:45, after the rebase onto the merged walk
(#126) and the two changes to the search over states that came with the
tactic; mode (b) runs with the leaf index (`checks index`).

- Mode (a) is cheap on the host: the dead-prefix trie skips 97.5% of
  Hectare's programs on core, and each checked program costs one round trip
  of 148 µs on average, of which the oracle's work is 79 µs. With a large
  library, Hectare's own enumeration is the cost: on the sweep, `firstJust`
  timed out after 742,000 programs, of which only 7,300 reached Lean.
- Mode (b) finds the programs that erasure loses (`+`, `Functor.map`). With
  the leaf index a state steps only the leaves whose result type can match
  its goal, but a goal that fits many leaves with open children (`α`,
  `Ordering`) still makes many states, and on the sweep those queries take
  15 to 29 s. The "use every argument" rule in the state is necessary:
  without it, mode (b) solved 18/22 on core and 10/22 on the sweep (before
  the index).

Per operation, Lean against GHC (warm figures; GHC from `cartProduct` on the
Prelude on the same machine):

| | Lean | GHC |
| --- | ---: | ---: |
| unification per step | 10 to 14 µs (`isDefEq`) | not timed apart (`tcSubTypeSigma`) |
| constraint call | 31 to 39 µs (`synthInstance?`) | 72 µs (`simplifyTopWanteds` in the implications) |
| snapshot and restore | 0.1 µs and 1.0 µs | 2.9 µs together |
| one checked program | 59 to 73 µs in the oracle, 122 to 140 µs with the round trip | in process |
| checks per second, mode (a) on core | 12,700 programs (32,000 steps) in the oracle, 6,800 with the round trip | |

`exact?` is not a substitute on these goals. With every argument required
(`exact? using`), it closes 17 of the first 20 goals, but its term is the
expected program for 2, and equal to it up to eta or by definition for 2
more. Without `using`, its terms are degenerate (`USize.size`, `Prod.snd p`).
`apply?` runs the same search and adds partial suggestions with open goals,
which a fit cannot use, so the spike compares with `exact?` only.

### The cost cascade, measured

Sums over the 22 queries, from `hectare-lean` with its `cascade` rows (runs
of 19:32 to 19:45 on the merged walk). The time of a level is per decision.
"Hectare" counts the programs that Hectare proposed; its time is the walk's
own figure for Hectare's construction, reduction, and listing. "Dead prefix"
is the walk's check time minus the round trips: the trie, the shared prefix,
and the bookkeeping. "Round trip" is the round trip minus the oracle's work.
A step that the arity check passes goes to the head check when it is on, and
then to `isDefEq`.

Mode (a), Hectare proposes, on core:

| Level | rejections | passes | time per decision |
| --- | ---: | ---: | ---: |
| erasure (once per query) | 110 constants | 1,562 constants | 26 µs |
| Hectare | - | 99,938 programs | 55 µs |
| dead prefix | 97,352 | 2,586 | 0.33 µs |
| round trip | - | 2,586 | 66 µs |
| arity | 197 | 7,261 | 3.4 µs |
| `isDefEq` | 0 | 7,261 | 10.4 µs |
| `synthInstance?` | 853 | 346 | 33 µs |
| complete, with `Meta.check` | 768 | 768 | 14 µs |
| snapshot | - | 7,458 | 0.08 µs |

On the sweep the shape is the same: Hectare proposes 1,029,177 programs at
43 µs each, the trie rejects 1,014,117 of them at 0.25 µs each, and 15,060
reach Lean, where `isDefEq` rejects 43 of 46,594 steps and `synthInstance?`
4,606 of 5,854 calls. The merged walk hands the host back at the root after
each new fit, so it steps more than the spike's walk did (7,458 steps on
core, against 6,041), with the same solved queries. Hectare's time is now
measured in the walk; most of it is the listing of the programs (3.2 s of
`firstJust`'s 3.7 s on core).

Mode (b), states from Lean's goals, on core, with each optional level:

| Level | none | head check | index | index and head check |
| --- | ---: | ---: | ---: | ---: |
| memo: splits rejected / passed | 33,362 / 16,348 | 33,362 / 16,348 | 33,362 / 16,348 | 33,362 / 16,348 |
| index: pairs rejected / passed | - | - | 874,043 / 193,372 at 29 ns | 874,043 / 193,372 at 29 ns |
| arity: steps rejected / passed | 52,498 / 1,441,855 at 1.7 µs | 52,498 / 1,441,855 at 1.6 µs | 0 / 620,310 at 1.6 µs | 0 / 620,310 at 1.6 µs |
| head: rejected / passed | - | 774,436 / 667,419 at 0.36 µs | - | 0 / 620,310 at 0.31 µs |
| `isDefEq`: rejected / passed | 928,303 / 513,552 at 5.4 µs | 153,867 / 513,552 at 5.7 µs | 106,758 / 513,552 at 5.5 µs | 106,758 / 513,552 at 5.5 µs |
| `synthInstance?`: rejected / passed | 67,466 / 8,152 at 8.1 µs | the same at 7.6 µs | the same at 7.5 µs | the same at 7.6 µs |
| complete: rejected / passed | 158,054 / 1,565 | the same | the same | the same |
| the 22 queries take | 18.6 s | 14.6 s | 11.4 s | 11.6 s |

The budget level rejects 18 states (more arguments to use than leaves), and
the memo answers 244,181 of its 257,712 lookups from the table. The steps
include the search's 426,938 steps on real goals, which no optional level
changes.

### The leaf index (mode b)

A new state no longer steps every leaf: it looks up its goal type in a
discrimination tree of the leaves' result types (`DiscrTree`, as `exact?` and
`apply?` index their candidates), one tree for each number of children, built
once for a search (191 entries in 1.4 ms on core, 1,220 in 8.2 ms on the
sweep). A lookup with `getUnify` keeps every leaf whose result may unify with
the goal up to reducible definitions, so the states and the transitions are
the same as without the index (on core: 13,531 states and 14,782 transitions
either way).

- On core the index skips 82% of the leaf and arity pairs at 29 ns each (2.3
  µs a lookup, one for each of the 13,531 states), and the 22 queries take 11.4 s instead of 18.6 s; the head
  check alone gives 14.6 s. After the index the head check rejects nothing,
  because the root key of the tree is the head, so the index replaces it.
- On the sweep, at 30 s a query, mode (b) with the index solves 20 of 22
  (with 4.8 million refine calls and 723,000 calls of `synthInstance?` over
  all 22): the index skips 83% of the pairs at 13 ns each, but 4.1 million of
  the 10.4 million steps still fail in `isDefEq`, because the heads match
  and the arguments do not. At 15 s (with the head check) it solved 17.

### When each mode wins, and how to combine them

Each query with each mode alone, 30 s a query (mode (b) with the leaf
index), from the runs above:

| query | (a) core s | (b) core s | (a) sweep s | (b) sweep s |
| --- | ---: | ---: | ---: | ---: |
| firstOr, lookupOr, countElem, dedup, sumAll, totalLength, catOptions, applyN, swapAll, replicateN | 0.17 to 0.24 | 0.17 to 0.28 | 0.33 to 0.54 | 0.36 to 2.18 |
| addPair, maxPair, compareLengths | 0.24 to 0.30 | 0.58 to 0.62 | 0.58 to 1.04 | 15.4 to 29.2 |
| takeDrop, allEqual, firstsOfZip, maxOrZero, containsEither, mapOr | 0.21 to 0.30 | 0.23 to 0.56 | 0.40 to 0.72 | 1.03 to 10.3 |
| firstJust | 4.13 | 2.13 | timeout | timeout |
| addPairPlus | other | 3.15 | other | timeout |
| mapFunctor | other | 0.18 | other | 0.41 |

Only mode (b) solves `addPairPlus` (core) and `mapFunctor` (both): their
intended programs use `HAdd.hAdd` and `Functor.map`, which have no erased
type. Mode (a) solves nothing that mode (b) misses, but on the sweep it is
about 27 times faster on `addPair`, `maxPair`, and `compareLengths`, whose
goals (`α`, `Ordering`) fit many leaves with open children.

The features, read before the search (`features` request, 1 to 12 ms a
query), with the names that the GHC side uses:

- **a higher-kinded variable**: the query or a leaf that fits the goal binds
  a variable whose type is a type former. True for `mapFunctor`, and also
  for `catOptions`, `takeDrop`, `swapAll`, `firstsOfZip`, and `replicateN`
  (and `dedup` on the sweep), where `Functor.map` or another leaf with a
  type-former variable fits the goal's `List` or `Option` head but is not
  needed.
- **a class over a type constructor**: the same queries (`Functor.map`'s
  `[Functor f]`), without `dedup`.
- **child goals that stay open**: the leaves that fit the goal with a child
  of a bare metavariable: 0 to 4 on core and 0 to 8 on the sweep, for every
  query but `dedup` and `sumAll`, with no clear line between the queries
  that mode (b) solves fast and those that it does not.

So on these queries the features do not separate the cases. The two queries
that only mode (b) solves differ by the leaves of their intended programs,
which a pre-search reading cannot see: `HAdd.hAdd` fits every goal, and
`Functor.map` fits every goal with a type constructor at its head. What does
separate them is the outcome of mode (a): it ends without the intended
program ("other") in 0.17 to 14.2 s, or it times out.

A portfolio uses that, and a classifier on the features does not beat it
(the measured times of each mode alone, combined per query; a total budget
of 30 s):

| strategy | core: solved, total s | sweep: solved, total s |
| --- | ---: | ---: |
| mode (a) alone | 20, 8.4 | 19, 9.9 |
| mode (b) alone | 22, 11.4 | 20, 105.3 |
| (a) for 1 s, then (b) | 22, 11.9 | 19, 38.5 |
| (a) for 2 s, then (b) | 22, 13.2 | 20, 10.7 |
| (b) for 1 s, then (a) | 21, 11.3 | 20, 20.5 |
| classifier: (b) first on a higher-kinded variable or a class over a constructor, else (a) for 5 s, then (b) | 22, 13.6 | 20, 24.5 |
| the faster mode for each query, known in advance | 22, 9.5 | 20, 10.3 |

"(a) for 2 s, then (b)" solves the union of the two modes on both libraries,
within 40% (core) and 4% (sweep) of the time of an oracle that knows the
faster mode. The classifier sends the constructor-headed goals to mode (b)
first, where `takeDrop` and `firstsOfZip` take 5 and 10 s on the sweep.

The portfolio, measured (`hectare-lean --portfolio`, 20:02; mode (a) for 2
s, then the search over states with the index in the same oracle, 30 s a
query):

| | core: solved, total s, median s | sweep: solved, total s, median s |
| --- | ---: | ---: |
| portfolio | 22 (19 by (a), 3 by (b)), 12.7, 0.22 | 20 (19 by (a), 1 by (b)), 10.2, 0.45 |
| mode (a) alone | 20, 8.4, 0.23 | 19, 9.9, 0.42 |
| mode (b) alone | 22, 11.4, 0.28 | 20, 105.3, 1.03 |
| the faster mode, known in advance | 22, 9.5, 0.22 | 20, 10.3, 0.42 |

Mode (a)'s outcome decides: `firstJust` (core) runs out of its 2 s and the
states solve it in 1.9 s more; `addPairPlus` and `mapFunctor` exhaust their
bound in 1.4 s and 0.2 s, and the states solve them. On the sweep the
portfolio is as fast as knowing the faster mode, because mode (a) solves 19
of its 20 and, on `mapFunctor`, ends in 0.36 s, after which mode (b) needs
0.07 s. On core it pays mode (a)'s time first on `firstJust` (2 s) and
`addPairPlus` (1.4 s). The same portfolio is the
default of `hectare?` (`budget := 2`): there it finds the intended program
for 19 of the 22 queries, against 16 for the search over states alone and 2
for `exact? using` (`cfta-lean/README.md`).

What could be host-agnostic:

- **The portfolio**: a schedule of proposers with budgets over one host
  `Checker`, with the outcome of each run (solved, exhausted its bound
  without the intended program, out of time) deciding the next. The walk's
  `Progress` already has the outcome (`progressOutOfTime`, the fits) and its
  `Limits` the budget. Mode (b) as a proposer needs the table of states in
  the generic code (with the host operations of mode (b): key, refine,
  sharing, decide), which the Lean prototype keeps on the Lean side for now.
- **The classifier**: a rule over a record of the three named features is
  host-free; each host reads the features with its own types and index (in
  Lean: the leaf index and a refinement step at the root; in GHC: the
  higher-kinded specializations at the query's type heads and the refinement
  hole fits). The rule tried here does not help on these queries, so the
  portfolio comes first.

### A tactic on mode (b)

Mode (b) needs no erasure and no second process, so in Lean it can be a
tactic: `hectare?` (`cfta-lean/oracle/Oracle/Tactic.lean`), the
counterpart of the GHC hole-fit plugin. It builds the states from the goal of
the tactic, with the locals of its context and the namespaces of its types as
leaves and the index of the leaves, and it gives the fits as `Try this`
suggestions. On the 22 queries it finds the intended program first for 6, in
the first five for 10, and at all for 16, where `exact? using` finds it for
2 (`cfta-lean/README.md` has the table).

## The refactor

The Haskell side is factored as proposed above, on the spike branch:

- `Data.CFTA.Gen.Synthesis.Walk` (in `cfta-generator`): `Role`,
  `Erased`, `proposals`, `Token`, `preorder`, `Checker`, `Extension`,
  `Hooks`, `Fit`, `Progress`, and `walk`. It depends on no host.
- `cfta-ghc`: `streamFits` builds a `Checker` over GHC's frames (the
  frozen variables before each step and the walker after it) and calls
  `walk`. Its API stays, and its behaviour stays: on nine Hoogle+ queries the
  size and result rows of the old and the new `hectare-ghc` are the same,
  with every counter but the times.
- `cfta-lean`: `streamFits` builds a `Checker` whose `truncate` records
  the depth and whose `extend` sends the depth and the tokens in one request
  to `lean-oracle`.

For mode (b), the proposal is a second module next to the walk, with a host
record of the four operations above (key, refine, sharing, decide) and the
snapshot pair, and a function that builds the table of states for a goal and
a bound and reads it as an ECTA (`Node Symbol`): a node per state, an edge
per transition and split, the sharing as equality constraints, and the
required arguments in the key. The ECTA's programs then go to the `Checker`
of mode (a), which ties what the table leaves loose: the open guards and,
until the sharing is encoded, the shared variables.

## Follow-ups

- For GHC, index the leaves of mode (b) as the Lean prototype does (a map
  from the result's type constructor, or GHC's own `TypeMap`).
- Encode the sharing as ECTA equality constraints, and build the ECTA from
  the table, so that mode (b) gets counts, ranks, and sampling.
- For an out-of-process host, batch several programs per round trip: the
  walk could send the next programs that no dead prefix covers, and the host
  answer each. This needs the trie on the host's side, or a speculative
  batch.
- Put the GHC step's unification time in its counters, so that the per-step
  comparison is complete.

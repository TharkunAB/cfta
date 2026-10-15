# cfta-lean

Component synthesis checked inside Lean's elaborator: Hectare's automaton
(`Data.CFTA.Gen.Synthesis` of [`cfta-generator`](../cfta-generator/README.md))
proposes programs over Lean constants, and a walk in Lean's `MetaM` checks
each program prefix by prefix. It is the Lean instance of the design of
[`cfta-ghc`](../cfta-ghc/README.md); [the note on host
checkers](../docs/host-checkers.md) compares the two.

The package has two halves:

| Part | Purpose |
| --- | --- |
| `oracle/` | A Lake project (Lean 4.35.0, core only) with the executable `lean-oracle`. It erases Lean types to Hectare's types, enters a goal's binders, and checks programs in `MetaM` over a line protocol on its standard input and output. |
| `Data.CFTA.Lean` | The Haskell client: it runs the oracle as a child process, reads the erased library and goal, and runs the walk of `Data.CFTA.Gen.Synthesis.Walk` with the oracle as its checker. |

## How a goal is filled

1. The oracle imports `Init` and erases the types of the library's
   constants (`Oracle/Erase.lean`): implicit type binders become type
   variables, instance binders are dropped, value indices of type
   constructors are dropped, and a constant with an explicit type argument, a
   proof argument, or a result of any type is left out.
2. The oracle elaborates the goal, as `∀ {α : Type} [BEq α] (x : α)
   (xs : List α), Nat`, and enters its binders: a type binder becomes a rigid
   type, an instance binder a local instance, and an explicit binder an
   argument that every program must use.
3. Hectare lists the programs of each size over the erased leaves, and the
   walk sends each program that no dead prefix covers to the oracle in one
   request: keep `k` frames, then step these tokens.
4. A step (`Oracle/Walk.lean`) gives the leftmost open goal a leaf with so
   many children: it instantiates the leaf's binders with fresh
   metavariables, unifies the result type with the goal by `isDefEq`, and
   gives each instance problem without metavariables to `synthInstance?`. A
   complete program has no pending instance problem, no metavariable left,
   and passes `Meta.check`. The oracle takes a snapshot (`saveState`) before
   each step, and restores it to backtrack.

## Running the benchmark

Build the oracle first, then the benchmark:

```sh
(cd cfta-lean/oracle && lake build)
cabal run hectare-lean -- core 30            # 22 queries, 30 s each
cabal run hectare-lean -- --search           # exact? on the same goals
cabal run hectare-lean -- --states core 25   # states from Lean's goals
cabal run hectare-lean -- --ping 20000       # a round trip and a snapshot
```

`--states` runs the second mode, without Hectare (`Oracle/States.lean`): the
oracle builds states from its own goals, memoized by the goal type up to the
renaming of its metavariables, the size, and the arguments still to use, and
searches them in preorder. Its leaves are every constant of the library, also
the ones without an erased type.

Each query also prints its cost cascade, a `cascade` row for each level
(erasure, Hectare, dead prefixes, the round trip, and the oracle's arity,
head, `isDefEq`, `synthInstance?`, and complete checks), with the rejections,
the passes, and the time per decision. The variable `HECTARE_LEAN_CHECKS`
turns on the optional levels of the oracle's step, separated by commas:
`head` compares the heads of the two types before `isDefEq`, `synthEnd`
leaves `synthInstance?` to the complete program, and `index` makes `--states`
look up the leaves of a new state in a discrimination tree of their result
types, as `exact?` does.

The benchmark runs from the repository's root, or with the variable
`CFTA_LEAN_ORACLE` set to the oracle's directory.

## The `hectare?` tactic

`Oracle.Tactic` has a tactic in pure Lean, the counterpart of the GHC
hole-fit plugin of `cfta-ghc`: `hectare?` proposes programs for the goal
from the locals of its context and from the environment, smallest first,
closes the goal with the first, and reports them as `Try this` suggestions,
as `exact?` does. Its search is a portfolio:

1. mode (a) for `budget` seconds: Hectare's programs over the erased leaves,
   from the program `hectare-propose` of this package (named by the variable
   `HECTARE_PROPOSER`), checked by the walk in Lean;
2. when that run exhausted its bound or ran out of time without enough
   programs, the search over states (`Oracle/States.lean`) with the index of
   the leaves, for the rest of `seconds`. It needs no Haskell and no
   erasure: implicit arguments, instances, and higher kinds are Lean's own.

Without the variable, or with `budget := 0`, only the search over states runs.

```lean
import Oracle.Tactic

example {α : Type} [BEq α] (x : α) (xs : List α) : Nat := by
  hectare? (suggestions := 1)
-- Try this: exact List.count x xs

example {m : Type → Type} [Monad m] {α β : Type} (x : m α) (f : α → m β) : m β := by
  hectare? (suggestions := 1)
-- Try this: exact x >>= f

example {α β : Type} (f : α → β) (o : Option α) : Option β := by
  hectare? (budget := 0)
-- Try these:
--   exact Option.map f o
--   exact f <$> o
--   exact (Option.map f o).getM
```

Its leaves are the locals that are values (not types, type formers, proofs,
or instances), the definitions and constructors of the namespaces of the
type constants in the goal and the locals' types and of the types that those
constants return (`Option` from `List.lookup`), and a few general functions
and class methods (`id`, `Function.const`, `BEq.beq`, `Add.add`,
`HAdd.hAdd`, `Max.max`, `Ord.compare`, `Functor.map`, `Bind.bind`, ...).

| Option | Default | Meaning |
| --- | ---: | --- |
| `size` | 5 | the largest program, in leaves |
| `suggestions` | 3 | the programs to suggest |
| `useAll` | `true` | every local must occur in a program, as Hoogle+ requires |
| `seconds` | 10 | the time of the search; it also stops at nine tenths of `maxHeartbeats` |
| `budget` | 2 | the seconds of mode (a) before the search over states; `0` for the search over states alone |

`OracleTest/Tactic.lean` has `#guard_msgs` tests: classes (`BEq`, `Add`,
`Zero`, `Max`), a higher-kinded goal (`Functor.map` on `Option`), a goal over
a monad variable, `useAll := false`, and a goal without a program. Run them
with `lake env lean OracleTest/Tactic.lean` after `lake build`.

Against `exact?` on the 22 queries of `hectare-lean` (`hectare-lean
--suggest 30 BUDGET`: `hectare?`'s portfolio with its own leaves, 30 s, every
argument required; `exact? using` with every argument required), on
2026-10-14:

| | `hectare?`, portfolio (budget 2 s) | `hectare?`, search over states alone | `exact? using` |
| --- | ---: | ---: | ---: |
| the intended program first | 6 | 6 | 2 |
| the intended program in the first 5 | 11 | 10 | 2 |
| the intended program found at all | 19 | 16 | 2 |
| median time to the intended program | 0.26 s | 0.38 s | 0.3 to 0.7 s |

Mode (a) first finds the intended program for `maxPair`, `compareLengths`,
and `firstsOfZip`, which the search over states alone does not reach, and it
moves `addPair` from rank 870 to 20 and `takeDrop` from 356 to 15; `allEqual`
(11 to 32), `totalLength` (14 to 33), and `containsEither` (35 to 68) move
back. The first program is the same for 16 of the 22 queries, and where it
changes (`compareLengths`, `takeDrop`, `allEqual`, `firstsOfZip`,
`maxOrZero`, `containsEither`) it is the intended program in neither run.
Mode (a) ends the search for 19 of the 22 (for `maxOrZero` at the cap of
1,000 fits, without the intended program). The search over states runs for
the other three: it finds `Functor.map f o` second for `mapFunctor`, and it
runs out of time on `firstJust` and `addPairPlus`, as it does alone.
`exact? using` gives the intended program for `sumAll` and `replicateN`, a
program equal by definition for `mapOr` (`Option.elim o d f`), and for the
others another program or none.

## Limits

- The erased types are first-order: a constant with an applied type
  variable (`Functor.map`, `pure`) has no erased type.
- Out-parameter classes erase badly: `HAdd.hAdd` has a result of any type and
  is left out, so a program adds with `Add.add`.
- There is no defaulting and no elaboration of numerals: a program that
  needs `OfNat` or a default instance does not fit.

# Changelog

## 0.1.0.0 - Unreleased

Initial version, for GHC 9.14 and Lean 4.35.0.

- `oracle/`: the Lake project of the executable `lean-oracle`. It erases the
  types of Lean constants to Hectare's first-order types, enters a goal's
  binders, and checks programs in preorder in `MetaM` over a line protocol:
  a step instantiates a leaf's binders, unifies its result with the goal by
  `isDefEq`, and gives the instance problems without metavariables to
  `synthInstance?`, and a snapshot (`saveState`) before each step lets it
  backtrack. Optional levels of the step (`head`, `synthEnd`, `index`) are a
  configuration, and each level counts its rejections, passes, and time. The
  oracle also has its own search over states of Lean's goals, and the
  requests `goals` and `transitions` of the generic one.
- `Data.CFTA.Lean`: the Haskell client. `withOracle` runs the oracle,
  `library` and `enterGoal` read the erased library and goal, and
  `streamFits` runs the modes of `optionModes` (Hectare's walk, mode (a), by
  default, and the search over states of `Data.CFTA.Gen.Synthesis.States`,
  mode (b)) as a portfolio with the oracle as the checker. `missingOracle`
  says why an oracle cannot run.
- `Oracle.Tactic`: the `hectare?` tactic, a portfolio of mode (a) (through
  the `hectare-propose` executable) and the search over states, which closes
  the goal and suggests programs as `exact?` does.
- The `hectare-lean` benchmark: 22 queries over Lean's core library, in each
  mode, with `exact?` for comparison. The `lean-tests` suite fills a goal in
  each mode, and is pending without the oracle.

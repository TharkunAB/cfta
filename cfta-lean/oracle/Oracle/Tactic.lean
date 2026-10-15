import Lean
import Oracle.Suggest

/-!
# `hectare?`: programs for a goal from its context

`hectare?` proposes programs for the main goal, in the spirit of `exact?` and
of the GHC hole-fit plugin of `cfta-ghc`: applications of the locals of
the goal's context and of constants of the environment, smallest first. It
uses the search over states of `Oracle.States` (mode (b)): each subgoal is a
state, built once, whose leaves come from a discrimination tree of the leaves'
result types, and each step is Lean's own (`isDefEq`, `synthInstance?`), so a
program has implicit arguments and instances filled as the elaborator fills
them.

The leaves are:

* the locals of the goal's context that are values: not types or type
  formers, not proofs, and not instances, which `synthInstance?` finds;
* the definitions and constructors of the namespaces of the type constants in
  the goal and in the locals' types (`List`, ...), and of the types that the
  results of those constants have (`Option` from `List.lookup`);
* a few general functions and class methods: `id`, `Function.const`,
  `BEq.beq`, `Add.add`, `HAdd.hAdd`, `Mul.mul`, `Max.max`, `Min.min`,
  `Ord.compare`, `Functor.map`, `Pure.pure`, `Bind.bind`, `not`, `and`, `or`.

The search is a portfolio: first mode (a) for `budget` seconds, Hectare's
programs over the erased leaves (from the program of the variable
`HECTARE_PROPOSER`, `hectare-propose` of `cfta-lean`) checked by the
walk; then, when that run exhausted its bound or ran out of time without
enough programs, the search over states for the rest of the time. Without
the variable, or with `budget := 0`, only the search over states runs.

The options are `size` (the largest program, in leaves, 5 by default),
`suggestions` (3), `useAll` (whether every local must occur in a program, as
Hoogle+ requires; `true`), `seconds` (10), and `budget` (2). The first program closes the
goal, and every program is a `Try this` suggestion. The search stops after
`seconds`, or when it has used nine tenths of `maxHeartbeats`, so a goal that
needs a long search needs a larger `maxHeartbeats`.
-/

namespace Oracle

open Lean Meta Elab Tactic

/-- Elaborate the options of `hectare?`. -/
declare_config_elab elabHectareConfig HectareConfig

/-- `hectare?` proposes programs for the goal from the locals of its context
and from the constants of the namespaces of its types, smallest first, and
closes the goal with the first one: mode (a) for `budget` seconds, then the
search over states. Options: `(size := 5)`, `(suggestions := 3)`,
`(useAll := true)`, `(seconds := 10)`, and `(budget := 2)`. -/
syntax (name := hectareTactic) "hectare?" optConfig : tactic

/-- `hectare?`: suggest the programs of the search, and close the goal with
the first. -/
@[tactic hectareTactic] def evalHectare : Tactic := fun stx => do
  let config ← elabHectareConfig stx[1]
  let goal ← getMainGoal
  let portfolio ← hectarePortfolio goal config
  let terms := portfolio.fits
  if terms.isEmpty then
    throwError "hectare? found no program of at most {config.size} leaves"
  if terms.size == 1 then Lean.Meta.Tactic.TryThis.addExactSuggestion stx terms[0]!
  else Lean.Meta.Tactic.TryThis.addExactSuggestions stx terms
  goal.assign terms[0]!
  replaceMainGoal []

end Oracle

# Source refresh through main 8f85ddb6

Main `eda6919b` (PR #54) is merged at `d27a38ec`.
Main `8f85ddb6` (PR #55) is merged at `7dccd588`.
The native intersection, constructor, equality, and Sized source bodies stay unchanged.
The optimized interned core and all older proof targets remain.

## Named measure terms

Commit `1b3ebf09` keeps a child named measure as a symbolic term when the
child comes from `every`. Previously this case could raise `InexactMeasure`.
The compiler substitutes the defining named terms before open integer counting.
The actual source also traverses conditionals and formulas during resolution.
The earlier folding proofs do not prove this entire new frontend.

The existing small sorted-list regression compares the symbolic and enumerated
languages. Both contain exactly 120 increasing triples over zero through nine.
The large regression counts 166666666666500000 triples over zero through one
million. Its final rank decodes to [999998, 999999, 1000000]. Both tests pass.

## Public typing automata

Commit `47b06bbe` changes `fromTypingRules` to accept a `Typing` record.
`typingAutomaton` returns the explicit constructor automaton.
`fromConstructorAutomaton` decodes an automaton after caller transformations.
`TypingState.Goal` stores the remaining nesting as `Maybe Int`.
The supported nesting bound uses `Just`. Nonempty inputs and `Binders` return
`NotImplemented` after constructor-name and field validation.

The finite needed-type description walk remains. It now returns needed type
descriptions, including atomic descriptions whose constructor list is empty.
Constructor positions still use each algebraic type's complete declaration list.
The previous typing proofs retain their modeled interfaces. The split public
wrappers, state representation, validation order, arbitrary constructor automata,
Generic codecs, and concrete container correspondence remain explicit adapters.
This source update does not close those obligations.

## Validation

The strict Nix build of all components passes with tests and benchmarks enabled
and `-Werror`. All six existing suites pass: 321 core, 231 generator, 169 refinement,
34 GHC-fit, and 22 decision-model examples, plus the hole-fit golden check.
The total is 777 examples plus golden. No local test file is changed.
Five changed Haskell files pass Fourmolu. All four active packages pass Cabal-gild.
The only Cabal-gild notices concern its deprecated `--input` spelling.

Evidence is in `lean/restart-evidence/20261016-physical/`:
source-pr55-strict-build.log, source-pr55-tests.log, source-fourmolu.log,
and source-cabal-gild.log. Earlier eda6919b build/test logs retain their own scope.
The Haskell fix handoff at the top of root FINDINGS.md records the failure cases,
files, commits, regressions, and upstream status for external work.

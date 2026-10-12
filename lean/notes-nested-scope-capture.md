# Pruning admitted an invalid nested-substitution term

`lean/repro/NestedScopeCapture.hs` uses the supplied Z3 backend. The grammar
has one underlying term. Two children are the same inner term named `a`, with
refinement `value = 0`. An outer scope substitutes `b` for formal `a`. An
inner scope substitutes the two actuals for formals `x` and `y`. The guard
then requires `x = 0`.

Sparse evaluation cannot prove that the two inner terms are identical. It
allocates `__microcfta_actual_0` and `__microcfta_actual_1`. The requirement
becomes `__microcfta_actual_0 = 0`, which follows from its actual assumption.
Complete evaluation merges the two actuals into the ambient name `a`. Its
requirement becomes `b = 0` after both scopes. The source deliberately keeps
actual assumptions ambient, so the available assumption is `a = 0`. The
complete query is false for `a = 0, b = 1`.

Before the repair, the repro printed complete/sparse guard verdicts
`(No,Yes)` and original/pruned membership `(No,Yes)`. Pruning removed the root
guard and admitted a term outside the original language. This is distinct
from the conservative Yes/Unknown spelling boundary in GuardAlphaBoundary.

The repair checks source actual ambiguity before invoking the sparse solver.
An ambiguous candidate receives Unknown. The existing fallback then returns
the original edge with its complete guard. This retains the library's public
complete evaluation and ambient-assumption semantics. It may retain a guard
which a more precise complete-identity analysis could discharge.

The existing PruneSpec now tests this exact grammar and rejected term.
After the repair, the standalone repro prints `(No,Yes)` and `(No,No)` and
exits successfully. The Nix test run passed 275 core examples, 193 generator
examples, and the 135-example refinement suite. Fourmolu and the microcfta
cabal-gild check passed.

`NestedScopeCapture.lean` records the original shared evaluator behavior.
Its callback decides only the two witness queries. `solver_sound` proves
that both decisions are correct over integers. `tables` computes the exact
sparse and complete allocation results. `verdicts` proves sparse Yes and
complete No by kernel reduction. This proves the obstruction without assuming
an SMT result. The Haskell repro separately confirms the supplied backend and
actual pruning path.

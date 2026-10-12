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

The earlier repair checked source actual ambiguity before invoking the sparse solver.
An ambiguous candidate receives Unknown. The existing fallback then returns
the original edge with its complete guard. This retains the library's public
complete evaluation and ambient-assumption semantics. It may retain a guard
which a more precise complete-identity analysis could discharge.

The existing PruneSpec now tests this exact grammar and rejected term.
After that earlier repair, the standalone repro printed `(No,Yes)` and `(No,No)` and
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

The generator compiler had the same invalid discharge. A direct six-child
recipe returns `Right []` from `validOutcomes`. Before the repair, compilation
returns cardinality one and the rejected tuple. `NestedCompileCapture.hs`
records this second public caller. The earlier `constraintDecision` checked
actual ambiguity before it invoked the solver. It returned `SolverUnknown` for the
unresolved group. This caller cannot retain a semantic guard in its output.
The error does not assert that the language is empty. It can also reject an
ambiguous group whose complete members would all be valid. Exact identity
splitting or complete-member checking would be required to compile that case.

`PruneAmbiguity.successful_ambiguity_restores` proves that every successful
pass with an ambiguous candidate returns the complete original edge.
`check_exact` requires semantic decision laws only for unambiguous candidates.
Those historical full-guard, candidate, and memoized models use that blanket
gate. Current `RecipeCompile.constraintDecision_accept` requires only sparse
Yes. The current compiler relies on runtime substitution safeguards; it has
no blanket ambiguity precheck.

The earlier complete Nix suites passed 604 examples after both caller repairs:
275 core, 193 generator, and 136 refinement. The compiler reproduction now
prints `Right []`, `Left SolverUnknown`, and `Left SolverUnknown`.

## Current scope checks

At `d6b8837`, `renamedByEnclosing` moved the rejection into the evaluator.
`SourceEnclosingRenames` executes that upstream policy and checks the original
nested witness as Unknown. It leaves complete term evaluation unchanged.

The rebase exposed a distinct same-scope case. `SameScopeIdentityCapture`
uses `[0->0, 1->4, 2->0]` and requires `a = 0`. Sparse evaluation retains the
first `a` replacement as a fresh name. Complete evaluation removes the first
`a->a` identity and selects the later `a->b` replacement. Both Lean and the
upstream Haskell source give sparse Yes and complete No. The supplied Z3
repro also showed pruning admit the term and compilation retain its tuple.

The current `ambiguousIdentityPrecedence` scan rejects an uncertain literal
identity when a later entry has the same formal name. It does not change
formula identity removal. `SourceSubstitutionPrecedence` proves the exact
ordered-pair predicate, preservation for known identities and distinct
formals, and unchanged complete evaluation. The two witnesses now give
sparse Unknown and complete No. `CurrentGuardPrune.same_scope_restores`
proves restoration of the original edge. The current compiler reports
`SolverUnknown`. See `notes-substitution-policies.md` for the remaining
non-injective query transport obligation.

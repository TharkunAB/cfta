Created: 2026-11-16 01:04 CET

# Earlier-isolation matcher normalization repair

UNCOMPILED. The original 232-line and repaired 241-line files remain immutable and uncredited. The public header, preamble and probe remain byte-exact.

Root check 79600 accepted the private prepared-action helper and all proof steps before line 191. Remaining failures came from unreduced literal outer matchers: the emitted `.done (..., some action)`, encoded `some newHandle`, and adapter `some attached` had not reduced before the next actual operation equation was used. Add one explicit `dsimp only` at each of those exact constructor branches. This makes each next scrutinee use the actual branch fields before applying its equation. The existing Right callback equation can then rewrite its literal call.

The nonreadable RESULT equality also retains a `let read` after unfolding. Add `dsimp only` there before splitting that actual read matcher. This is the explicit RESULT equality, not the outer isolation predicate that caused the earlier split error.

These four proof-only normalization commands are the entire raw delta from the 241-line repair. No source semantics, original fuel, public premise, endpoint, linter or compiler-budget setting changed. No compiler was invoked.

Current proof update: 2026-10-21 02:57 CEST. Proof checkpoint: `e4b2683f5`.
Actual source-started native traces now derive exact positive positions
for the SAME stored Mu finish. PositiveAt finish p iff smart=true,
decoded local-use=false and PositiveAt ordinary-probe p. Nested syntax
and earlier warm winners are included. No caller unused flag is assumed.
Root strict, complete two-head readback, independent review and Audit pass:
3561 jobs and 74571 dependencies, only the old ClosedCompletion warning.
The theorem concerns stored readback. It does not prove completion or
positive support for an arbitrary whole native output.

No Haskell source, runtime result or external fix changes.
Preserve PR #97 and every earlier repair and reproducer below.
The remaining local bridge is ordinary-probe positions back to the incoming
maybeMu body under actual Cap/binding and encoded-callback facts. Native
request/cache transport, chronological edits, renewal, retention, outer
completion, convergence and Haskell refinement remain open. The full goal
stays active. Read `lean/notes-current-stored-mu-position.md`.

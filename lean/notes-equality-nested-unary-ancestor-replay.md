# Actual-cache unary ancestor replay checkpoint

The user requested wrap-up during the final semantic composition.
The following three modules are frozen at their last successful builds:

- `EqualityNestedUnaryAncestorReplay`: `actual_original` proves that the
  actual returned edit cache replays the complete parent built from all
  original transformed unary rows. It also replays every original child
  and rebuilt edge request. No later preparation cache is required.
- `EqualityNestedUnaryAncestorState`: `Stored` retains original finite
  indices as exact closed edge requests and a closed parent request.
  `edit_stored` derives this representation after the actual source edit.
  `project_complete` reads the exact indexed projection from such a parent.
- `EqualityNestedUnaryAncestorEdit`: `node_eq` proves exact equality between
  the actual optional source unary path worker and finite constructor work.
  `node_complete` derives facts, preparation, histories, and result
  availability from concrete nested endpoint intersections.

Validation: Lean 4.34.1 built the three-module import closure in 400 jobs.
The final aggregate audit includes these modules and checks 36,839 theorem
dependencies in 1,026 jobs. Only the three standard axioms are allowed.
The log is `/tmp/mcfta-20261013-final-restart-audit.log`. The earlier
ancestor helper checkpoint had its own audit of 15,449 dependencies.
No build or audit is currently running.

The marked file `MicroCFTA/EqualityNestedUnaryAncestorEditCompletion.lean.draft`
preserves the unfinished `edit_complete` composition. It is excluded from
the checked Lean module tree. It is not a proved theorem. The proof attempts
to use `complete_mono`, but that helper does not pass the completed execution
equation to the stronger postcondition. The attempted `exactWork` equation
therefore cannot be derived from its local context.

Next: destruct `node_complete` directly into its concrete output, returned
cache, execution equation, and extension. Rewrite `node_eq` with that exact
run. Apply `edit_stored`. For each original index, apply the frozen
`EqualityNestedUnaryWorkFacts.meet_correct` in the returned cache, then
rewrite by the completed original child request. This derives the updated
row representation without a later cache.

After that, compose both actual forest-entry edits and the root identity
stop test. A changed root implies a changed indexed endpoint state because
closed original row requests determine the same canonical parent when all
endpoint values agree. This permits the existing generated-row loop bound
to bound the source root loop. No complete root-loop theorem is claimed.

## Current plain row owner exclusion and actual branch classification

Updated: 2026-10-21 01:30 CEST. Proof checkpoint: `7e4228593`.
Verified start: `b514e9409`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-plain-owner.md`.

An actual plain row dispatch now excludes its active ordinary owner's
value reference and complete cache key. The owner can have any ready
inherited constraint. Actual cold writes and warm hits retain the same
captured row's original, erased or sentinel children. Actual earlier
siblings can return before the selected dispatch. No enclosing return
or selected child return is required.

Actual local and Parent successes now supply their branch classification.
The selected arm retains the same field load, precheck, Scan, Required,
class pass and accepted constructor, with their exact states and memos.
An empty selected list can propagate Empty. It need not return unchanged.

A closed binary example creates an actual cold edge cell, activates its
owner, reads that same warm cell, completes slot zero and reaches slot
one. It retains the generic reference and key inequalities. Strict and
complete public readbacks pass. Aggregate Audit passes: 3546 jobs and
74380 theorem dependencies, with only the old ClosedCompletion warning.
Earlier checks and failed attempts remain. Counts do not measure completion.

The main gap is constrained copying: an actual copy of the active Top
owner must retain a same-child equality after descent, or be excluded.
The new classifiers expose that execution but do not prove this claim.
Causal selected receipts at warm readers, general renewal, final retention,
outer completion, convergence and production Haskell correspondence remain
open. Native initial_complete keeps its existing closed syntax scope.
No Haskell source or runtime result changes. FINDINGS retains all external
repairs first. The whole-library goal stays active. Pushes remain authorized.


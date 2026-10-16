# Edit and Class/Pass profile validation

2026-10-16 22:35 CEST.

Final production sources:

- EditProfiles: 300 lines, SHA256 `85f3af54349469fbb308de38d5a4aa1c39f4436c8cc3e65f3875ac52a09f6b53`.
- ClassPassProfiles: 107 lines, SHA256 `d9e8ffc66d0043e15ee5a0417f30cf2259999f5a7fe42843313a2d6c36fffbe9`.

Direct final checks use pinned Lean v4.34.1 with unused-section and unused-variable linters. Edit direct attempt 2 and Class/Pass direct attempt 2 exit 0 with no diagnostics. Class/Pass attempt 1 used an incorrect namespace import for `compiled`; its source and error log remain.

The first root canonical builds completed successfully: Edit 1322 jobs and Class/Pass 1333 jobs. They exposed three private Edit argument warnings. The final Edit source renames those unused binders. The final joint canonical rebuild passes 1333 jobs in `edit-class-profiles-build-2.log`, with no new warnings. The older dependency's unused `inputs` warning remains outside this change.

Public probes report all seven theorem signatures with explicit arguments, universes, full names, deep terms, and proof output. Every theorem has an axiom report. Final imported public logs are `edit-profiles-public-2.log` (4 pairs) and `class-pass-profiles-public-2.log` (3 pairs). Final `edit-class-profiles-kernels-3.log` has 4 integration pairs. All three logs exit 0 with no diagnostics or sorryAx. Their only axioms are propext, Classical.choice, and Quot.sound. The final external kernels check four exact source cases:

1. Empty below-edits construct an unchanged Node graph and reads, with no leaf query.
2. Child-list root leaves construct the source skip graph and reads at the identical full shared state.
3. Two actual Leaf receipts construct ordered selected-child reads. The second receipt starts at the first receipt's exact returned state and global bundle.
4. Two actual Class read graphs construct a tail-first Fold and final Pass. The new strong stores join the existing semantic receipt and positional narrowing at the SAME result, checked state, and Merge memo.

The kernels verify supplied component receipts. They do not assume a completed enclosing Edit/Pass, a future callback, or a result profile. The first kernel attempt used a bare `trivial` term where the recursive Populated definition needed explicit simplification. Its source and failed log remain. The corrected kernel source is unchanged after attempt 2.

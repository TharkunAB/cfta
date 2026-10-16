# Original native entry validation

Validated 2026-10-16, Europe/Stockholm.
Source main: `8f85ddb605327bd088aae970ab058137c4f6d762`.
Starting published proof: `8ec2983b2b617acc71c7f495a8df14f5513b04c4`.
Proof commits: `07ef6169`, `13950ca4`, `c585a6d3`.
Audit and scope note: `6591e383`. Restart documents: `f360d515`.

## Successful authoritative outputs

- full-audit.log: terminal 0; 2299 jobs; 56075 theorem dependency checks.
- preparation-build.log: terminal 0; 1214 jobs.
- preparation-probe.log: terminal 0; seven public declaration axiom reports,
  seven signatures, three kernel examples, and three executable evaluations.
- history-build-20261016.log: terminal 0; 1235 jobs.
- history-public-probes-20261016.log: terminal 0; five public axiom reports,
  five signatures, nine kernel examples.
- prepared-history-build-2.log: terminal 0; 1280 jobs. Both root composition
  modules build in this dependency graph.
- root-probes-1.log: terminal 0; two public axiom reports, two signatures,
  one kernel example, one named kernel theorem, and its axiom report.
- class-build-1.log: terminal 0; 1236 jobs.
- class-probe-3.log: terminal 0; four public axiom reports, four signatures,
  thirteen kernel examples.

Total: 18 public reports, 18 signatures, 26 kernel examples, one named
kernel theorem, and three executable evaluations. The named theorem adds
one axiom report. Only propext, Classical.choice, and Quot.sound occur.
Canonical builds replay the existing unused-input warning from
InternedFreshOrdinaryClosedCompletion. No new warning occurs.

Pinned aggregate command:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

Focused builds use the same executable with the named module. Public probes
ran from the lean directory with that lake executable and `env lean` on
the repository-local probe path. Saved intermediate failure logs remain
unchanged. They are not successful proof evidence. Final green log names
are listed above. No probe file is imported into the library Audit.

## Required behavior and reviewed scope

History events retain each actual original constructor and normalized
field check. History coverage derives normalized source syntax and earlier
field origins. Actual construction transfers them to every physical edge
record. Same-cache read-only loads follow. OriginalHistory.constructed
therefore derives Good, SemanticReady, availability, closedness, and Original.

Preparation runs each actual field constructor in list order and retains
the caller's interner. It derives finite completion, actual causal History,
atomic steps, final validity, and ordered ready/readback/load receipts.
Executable cases retain duplicate canonical identities, earlier entries,
the first malformed-field error and reached cache, and contradiction.

ConstructedHistory derives the native invariant bundle from the covered
history and actual source build. Closed available selected operands derive
Original syntax from heap coherence. The finite full operand list derives
the input model. PreparedHistory also derives its own preparation completion
and history. Both its range premise and actual query receipt use the literal
returned cache projection `(prepare (guards expression) initialCache).2`.
No initial Good, SemanticReady, desired output law, model-validity callback,
or future successful query is supplied at this composed entry.

The named kernel theorem derives actual checked serial completion, stability
under extra fuel, final physical and semantic invariants, closed available
results, ordered independent intersection languages, and unchanged two-step
warm repeats directly from PreparedHistory.query_complete.

The actual source build, initial cache validity, normalized fields for
Preparation, closed available operands in that common source, and reached
WordRanges remain explicit. Normalization is not inferred from interning.
Preparation is one finite serial schedule. It does not prove Haskell's
lazy field-demand schedule. The retained equality interner is not reset.
Only modeled completed operation tables start empty. This is a cold checked
projection, not a reset of Haskell global caches or an arbitrary warm-table
validity theorem.

ClassHistoryEntry also derives successful field loads and finite exact
allocated precheck behavior. Its two Scan endpoints retain the actual live
prefix and completed historical Scan explicitly. That Scan still uses the
older native-intersection emptiness decision. Current conjunction-based
Decision/Scan correspondence and general constrained completion remain open.

Independent read-only reviews are history-root-review.md,
preparation-review.md, and class-review.md. No material defect was found.
Frozen reviewed source hashes match frozen-modules.json.

## Preservation and source status

preservation-final.json checks the 3347-file starting manifest. No file is
missing. All 2293 older non-Audit proof sources retain identical bytes.
All seven earlier frozen manifests pass. Only the seven restart documents
and additive Audit imports change among baseline files. Stashes and other
worktree records remain unchanged. Earlier unavailable external draft bytes
are not claimed recovered or reverified.

No Haskell implementation or test changes occur. The diff against main
still contains only the historical constructor changelog entry and the
equality reproducer comment. The Haskell fix registry remains near the top
of FINDINGS.md, with failure cases, paths, commits, checks, and upstream
status. Reuse the unchanged-source strict Nix all-component build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild
evidence recorded there. Those checks were not repeated.

All owned process handles are terminal. This checkpoint is concrete progress.
The full-library goal remains active. Next connect the current conjunction
decision and memo/worklist effects to class Scan, then compose current
checked native callbacks, selected required paths, and the general
constrained outer caller. All other full-library and separate Sized targets,
runtime publication, concurrency, containers, machine bounds, warm operation
tables, generated operands, and cross-model admission retain their scope.

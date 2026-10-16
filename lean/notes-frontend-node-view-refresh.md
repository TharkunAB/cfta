# Generator node views and source refresh

## Source boundary

Source main `999c04a5` is merged into formalize at `9aaffc95`. The preceding
published checkpoint is `b931bcc6`. The backup branch is
`backup/formalize-before-main-999c04a5-20261016-1301`.

PR #60 (`d0966953`) adds field-specific atoms. Annotations now use exact
`Constructor` keys. A field pool applies before a type-wide atom. PR #61
(`9968bd8e`) writes typing rules through node views and extracts constructor
and field positions with `nodeFields`. PR #62 (`443e3458`) rejects negative
`Nesting` and `Binders` bounds before node-view validation. Root FINDINGS.md
records that repair first, with its failure, regression, files, and upstream
status. No local Haskell repair is added by this refresh.

The upstream delta changes nine generator files, including seven Haskell
files. The interned core, equality implementation, Sized, GHC package,
decision model, and Lean sources do not change. The retained constructor
changelog entry and equality reproducer comment remain the only local
differences in the four active Haskell package trees.

## Proof state and objective

The complete pinned Lean Audit still passes 2444 jobs and 58082 dependency
checks. These are preserved component proofs. The refresh adds no theorem
for the new frontend APIs. Existing typing proofs use resolved labels and
fields. New node extraction, validation order, bounds, inputs, binder states,
field pools, codecs, and public wrapper composition still need current-source
adapters. The audit notes in the evidence directory record the precise
source changes and boundaries.

In particular, a new typing variable callback can choose its constructor for
each reached index and type. The old resolved-row model fixes one label for
that schema. It needs per-reached-node resolution. Reached callback fields
now validate before bound filtering. A malformed callback that bound zero
would discard can therefore report `FieldMismatch`. This affects error
behavior; it is not a wrong language for valid typing rules.

The focused recursive-field-pool reproducer confirms a separate contract
gap. A field pool can supply `End False` below `Next` when the invariant
requires `End True` at every node. The derived generator includes that term,
and `holds` returns true for it. Root FINDINGS.md records the exact program,
output, source locations, and unfixed status. The intended treatment of
supplied recursive subtrees must be explicit before a frontend theorem or
behavior repair. Existing suite success does not settle that contract.

The full objective is correspondence between the specified constrained tree
languages and generators and the current Haskell library. This requires
separate results for exact transformations, finite execution, accepted terms
in each size class, counts, ordered ranks, both inverse laws, and probability
laws. Accepting runs, distinct terms, and generated values remain different
objects. Passing suites and the theorem total do not establish this objective.

The current `SourceCurrentAllocatedPartialActual.root_exact` theorem proves
language equality and retained caller invariants for a completed outer call
with strict source reads, actual checks, and legitimate initial facts. It
does not construct general constrained outer execution. Literal workers now
cover merge, Target, shared leaves, edits, class passes, and conjunction rows,
worklists, decisions, and the fourth memo. Their serial model does not prove
GHC demand, lazy publication, concrete host global-table events, or the
`noConstraint` CAF. Conjunction true proves emptiness. False does not prove
nonemptiness.

## Validation and preservation

Current source commands, logs, suite counts, audit results, and source hashes
are in `lean/restart-evidence/20261016-frontend-node-view-refresh/`.
`source-validation-inputs.json` records the exact Nix commands.
The strict all-component build passes with tests and benchmarks enabled and
`-Werror`. All six suites pass 791 examples with zero failures, plus golden.
The seven changed Haskell files pass Fourmolu. The four active packages pass
Cabal-gild and metadata checks. No test file is added or changed locally.
`verify-preservation.py` compares all 5097 starting tracked files. It permits
only the nine exact upstream paths and the seven restart authorities to
change. All 2443 older non-Audit proof sources and Audit retain their bytes.
Twenty-five frozen manifests check 201 module entries. All previous repair
bullets and the PR #55 handoff remain byte-identical. Stashes and the three
other worktree records remain. The new negative-bound repair is added above
those historical entries.

Raw `starting-worktrees.txt` retains the blank separator from git porcelain.
Exclude that raw capture from source whitespace checks. Do not remove failed
drafts or raw validation evidence. Earlier unavailable external drafts remain
unavailable; this refresh makes no recovery claim.

## Next proof

Read `lean/restart-evidence/20261016-current-conjunction-worker/scan-worker-next.md`.
Its source baseline is historical; its next proof target remains current.
Implement the literal first-seeded projection and checked intersection,
then current Scan with strict primary reads and the literal fourth-memo call.
Project without `mergeAlternatives`. Preserve the first-seed rotation, actual
head/tail/native states, failure states, class order, and early stop.
Derive stable execution and full caller receipts from legitimate initial facts.

Then compose local reduction, required children, parent construction, and the
mutual outer worker. General constrained outer termination, unequal-length
path classes, and repeated-pass convergence remain open. Current
`reducePartially` performs one pass. All frontend, Sized, generator, probability,
solver, callback, codec, concrete-container, identity, concurrency, machine,
host-runtime, and older constructor/equality obligations remain active.
Preserve the optimized interned core and all local proofs, counterexamples,
repairs, and marked drafts. Push verified formalize checkpoints regularly.
No board posts or deployments. This checkpoint is progress; the full goal
remains active.

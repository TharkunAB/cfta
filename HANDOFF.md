# microcfta formalization handoff

Updated: **2026-10-13 02:10 CEST (Europe/Stockholm)**.

## Scope and authorization

Matti requested continued formalization after the findings repairs merged.
The required properties remain:

1. Compile constrained languages to exactly their valid finite terms.
2. Prove enumeration sound and complete. Exact optimizations must retain
   every required term and its weight.
3. Give each distinct accepted FTA term one rank and prove both inverse
   laws. Keep generator member multiplicity separate from distinct terms.
4. Prove requested probabilities. State algorithmic costs separately from
   a materialized reference enumeration.
5. Compare the executable Lean definitions with the current implementation.
   Keep representation and external contracts explicit.

Continue within this scope. Local proof work and source repairs are
permitted. No push or deployment was requested for this continuation.
An active user-requested goal requires continued work until the formalization
is complete. Record repairs in `FINDINGS.md`. Do not stop at a proof checkpoint.

## Repository and rebase

- Repository: `/home/tritlo/Code/mcfta`; Ubuntu/WSL2, Bash.
- Branch: `formalization/microcfta-resume-20261012`.
- Base: `origin/microcfta`, `de910ea` (merged findings fixes through PR #96).
- Earlier proof integration checkpoint: `2c469d4`. Subsequent local commits
  add logical read transport, plain application, and nested constructor replay.
- Other continuation commits: `3d3724f` (keyed families), `ee29250`
  (current equality), `840185a` (total substitution), and `d783309`
  (same-scope source repair and proofs).
- Previous branch `spike/microcfta-lean-soundness` remains at `c2b1c0f`.
- Backup: `backup/lean-before-microcfta-20261012-2200`.
- The retained stash has message `Preserve pending keyed nary and recursive
  join proofs before microcfta rebase`. It contains the original untracked
  files. They were restored successfully; keep the stash as a backup.
- The separate worktree at `/home/tritlo/Code/microecta/lean-fixes` was not
  changed.

`git pull --ff-only` succeeded after retrying the read-only `.git` failure
with the required access. It fetched the current `microcfta` base. The
continuation branch replayed 175 proof/documentation commits. Historical
patches under `microcfta/` and `microcfta-generator/` were retired because
upstream contains the revised repairs. Mixed commits retained their proof
and reproduction changes. Verification before new work confirmed every
tracked proof byte matched the previous branch. Production Haskell matched `origin/microcfta` exactly after the rebase.
The local repairs change sparse substitution in
`microcfta/src/Data/CFTA/Refinement/Evaluate.hs` and recursive construction
queries in `microcfta-generator/src/Data/CFTA/Gen/`.

Do not replay the old source fixes over this base. In particular, upstream
changed total formula substitution, sparse nested-scope decisions, the
recursive equality gate, equality constraint interning, and top-level
self-reference removal from recursive unions.

## Verified checkpoints

- Existing Haskell suites on `de910ea` plus the local repairs: **620 passing
  examples** (284 core, 194 generator, 142 refinement). Existing cases were
  extended; no new test file was added. Log:
  `/tmp/mcfta-construction-query-full.log`. After the grouped-discovery check,
  all generator and refinement cases pass in
  `/tmp/mcfta-family-discovery-validation.log`. Core source is unchanged.
- Latest integrated Lean build: **726 jobs; 31,947 theorem dependency checks**.
  This includes projected leaf schedules, nested first-run completion,
  stored shallow unfolding, and construction-query provenance.
  Log: `/tmp/mcfta-runtime-bound-normalization-audit.log`.
- The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
  It rejects omitted proofs, native evaluation axioms, and custom axioms.
- Retained `FormulaCapture`, `NestedCompileCapture`, `RecursiveReduction`,
  and `OpenUnion` probes all pass on the new base. The two-key recurrence
  checks eight classes and 285 inverse ranks, exact masses, conditional
  probabilities, and support acceptance again.
  Log: `/tmp/mcfta-de910ea-focused.log`.
- A new independent heterogeneous `Bool`/expression join recurrence checks
  eight classes, 37 member inverses, exact masses, and support acceptance.
  Files: `/tmp/mcfta-heterogeneous-join-replay.hs` and `.log`.
- Source inventory: all **66 Haskell modules** occur in `API-COVERAGE.md`.
  Report links, import closure, and the whitespace check for this
  continuation (`git diff --check 3d3724f^ HEAD`) pass. The full diff against
  upstream retains 12 pre-existing blank-line-at-EOF warnings. The same
  warnings occur in the preserved pre-rebase proof branch; see
  `/tmp/mcfta-whitespace-baseline.log`. Those unrelated files were not edited.

Commands:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
```

Use Nix for Haskell. The PATH addition selects the coherent linker/GMP
setup. Nix lock access requires escalation. Fourmolu and both audited package Cabal-gild checks pass. No Cabal file
changed. The local production changes are the three repairs below. Do not rerun the whole Haskell suite
without a new source change or finding.

## Completed proof work

The formerly untracked `KeyedGuards` and ten `KeyedNary*` modules are
committed and audited. They prove flat mutual-family record equations,
retained masses, all-view inverse queries, candidate bounds/order/distinctness,
bounded global ranks, and original typed guard metadata. Raw singleton
choice differs from bare singleton same-key merge. Label term growth differs
from plain pay. See `notes-keyed-nary.md` and `notes-keyed-nary-guards.md`.

All fifteen `RecursiveJoin*` modules are committed and audited. The broken
record bridge is fixed. Typed bodies now compose nested heterogeneous joins,
labels, maps, pays, applications, and flat choices. The family proofs derive
independent count/decoder/mass/sampler fields, finite derivations, and source
knot equations. Mutual callback induction proves all-view inverses. Public
bounded queries preserve exact preimages and ascending distinct ranks.
Candidate bounds include false flags. These laws use only local finite-leaf
callback contracts. `RecursiveJoinGuards` derives the family guards from
original label-aware metadata and the public combined check. See
`notes-recursive-join-fields.md` and `notes-recursive-join-guards.md`.

`BinderSelfUnion`, `ConstrainedRecursionGate`, and `EqualityIdentityMemo`
cover the current equality and binder policies. The old recursive barrier
remains explicitly historical. Current source can unfold an open
unconstrained binder at the same path. A rank for those unfoldings is an
explicit remaining premise. See `notes-current-recursive-equality.md`.

`FormulaTotalSubstitution` and `IntegerLabelTotalSubstitution` cover the
current total APIs. Checked substitution traverses arguments before reporting
an unsupported function head. Total substitution retains that head and
traverses its arguments. General simultaneous semantics applies on the
checked-success domain, not to arbitrary fallback results.

`SourceEnclosingRenames` retains the upstream safeguard policy.
`SourceSubstitutionPrecedence` models the repaired evaluator below.
`BooleanGuardCompile` now uses actual evaluator verdicts, without a fictitious
blanket ambiguity precheck. `CurrentGuardPrune` likewise evaluates first and
checks ambiguity only after Unknown. Its general language theorem requires
unambiguous specialization cells. Earlier blanket-gate modules remain
historical. See `notes-substitution-policies.md`.

The aggregate includes the independent, erased-edge, and retained-reference
nested completion proofs. The last class covers arbitrary nesting depth with
one symbol, using actual live enclosing references instead of fresh marker
symbols. Stored shallow Mu unfolding now derives its preparation and strict
head-rank decrease from source constructor invariants. Projected leaf equality
schedules have a derived pass bound and physical normalized-parent readback.
The more general cases remain active.

## New source repair: duplicate-formal identity precedence

`de910ea` still admitted an invalid term when one flat scope had replacements
`a0 -> a`, `a1 -> y`, and `b -> a`. The first two actuals are equal non-leaf
terms named `a` with refinement `value = 0`. The guard requires `a = 0`.
Sparse evaluation retains a fresh first replacement and says Yes. Complete
evaluation removes the identity `a -> a`, exposes `b -> a`, and says No.
Pruning admitted the rejected term; compilation produced an invalid singleton
although `validOutcomes` returned `Right []`.

`SameScopeIdentityCapture` proves this counterexample with a sound callback.
The source repair `d783309` adds `ambiguousIdentityPrecedence`. It returns
Unknown when an uncertain literal identity has a later replacement for the
same formal. Complete evaluation, known identities, and unique formal names
retain their behavior. Both the old nested and new flat-scope cases now give
`(No,Unknown)` for complete/sparse evaluation and `(No,No)` before/after
pruning. Compilation reports `SolverUnknown`. The helper scan, unchanged
complete evaluation, explicit Unknown witnesses, compiler rejection, and
original-guard restoration have checked proofs.

The existing `NestedScopeCapture.hs` and `NestedCompileCapture.hs` now cover
both cases. Existing GuardSpec, PruneSpec, and CompileSpec cases were extended.
Logs: `/tmp/mcfta-same-scope-source.log` and
`/tmp/mcfta-same-scope-compile.log` before repair;
`/tmp/mcfta-scope-precedence-repaired.log` afterward.

## New source repair: recursive construction queries

Row 19 in `FINDINGS.md` retains a public callback that inspected temporary
support and returned inconsistent record fields. The repair adds independent
construction tokens to recursive records. Queries reject active placeholders.
Completion removes the owning token and keeps enclosing tokens. This applies
to both cyclic and unused-occurrence return paths. The latter is needed when
a nested family selects a closed key from an outer definition.

`RecursiveConstructionQueries` proves exact marker provenance, stable query
rejection, nested completion, and unchanged completed payloads. The existing
GenSpec recursive-member case checks fourteen observations, the original
callback, and nested selected-key completion. See
`lean/notes-recursive-construction-queries.md` for the source correspondence
and remaining arbitrary-callback boundary.

## New source repair: stale grouped discovery minima

Row 20 retains a public callback whose finite base changes after initial key
discovery. The source previously returned minimum zero with no size-zero
member. It now compares the final probe table with the accumulated table and
reports `InconsistentRecursiveFamily` on disagreement. `GroupedProbeValidation`
derives the actual fixed-point condition and proves unchanged results for
monotone constructor programs. See `lean/notes-grouped-probe-validation.md`.

## Remaining proof boundaries

- General termination of explicit equality/pruning fixed points on finite
  DAGs remains open. Finite language size is insufficient. The retained
  six-round example grows representation size. Complete canonical leaf
  forests with multiple symbols now have a proved bound for simultaneous
  class edits and empty propagation. Both 4,096-input source comparisons pass.
  Disjoint binary direct-root classes stabilize in one changing pass even
  with nested domains. Projected leaf occurrences have a separate weight
  bound for the full schedule. Their physical normalized-parent adapter and
  recursive finite child transformations now compose in a generated common
  cache. Physical leaf intersection and projected union now have exact
  readback for canonical admitted inputs. Source checks derive admission;
  raw initial guards have a separate proved progress phase. Their physical
  constructor preserves rejected sentinel allocations and derives exact raw
  readback and the whole-node identity shortcut. Physical Cartesian readback
  and strict rank decrease now follow for raw inputs. A finite raw inventory
  retains initial syntax and every later canonical conjunction. Finite
  occurrence compilation and actual recursive workers now derive complete
  payload availability and readback. Finite raw leaf intersection and union
  now derive complete-record correspondence in generated later caches.
  The complete recursive required-path worker corresponds to retained
  occurrences without an assumed worker law. Endpoint projection, seeded
  target folds, and simultaneous recursive edits now derive exact records.
  Raw leaf pullback and occurrence trimming remove temporary proof-cache
  allocations. The next runtime pass can use its actual preceding cache.
  Trimming preserves leaf endpoints and the occurrence progress measure.
  The complete physical class schedule and pass now compose. Repeated passes
  reach an allocation-free physical fixed point within the initial occurrence
  weight plus one. Normalized source constraints derive proper paths. Ordinary
  records derive the recursion-filter fast path. Source operand ordering and
  ordinary union cache effects have exact correspondence proofs. See
  `notes-equality-leaf-runtime-bound.md`. The existing 4,096-forest source
  comparison and 1,156 raw leaf pairs pass again after these model repairs.
  Arbitrary nested intersections
  can cycle when operands alternate; the fixed schedule remains unresolved.
- The new recursive equality gate can unfold an open unconstrained binder
  at the same path. LexicalGateRank now derives head-binder decrease for
  the full lexical reconstruction. Actual smart-node and nonsingleton-union
  branches are proved. Actual stored shallow bodies now derive normalization,
  successful substitution preparation, and strict head-rank decrease.
  Full nested stored-Mu preparation now preserves cache and record invariants.
  Cached free metadata derives exact source binding restriction. General
  strict unfolding rank and language correspondence still need composition.
  A concrete `UnfoldingRank` now follows from actual stored records when all
  completed Mu bodies in the cache have depth zero. It derives completion
  and eventual fuel equality without a supplied rank or decrease law.
  The reachable-only version now derives these results with unrelated deep
  records in the same cache. Reachable Mu bodies must still have depth zero.
  A separate actual completion and strict-decrease theorem permits arbitrarily
  deep closed nested Mu records inside an ordinary body. General open nested
  preparation remains unresolved. Source marker provenance also derives
  one-step completion and rank decrease through open nested Mu records.
  It does not prove closure of the marker condition under repeated unfolding.
  A separate unrestricted executor example increases head rank. Its callback
  violates the documented substitution-parametricity precondition, so it is
  not an admissible-callback defect. Actual free-reference occurrence costs
  now have normalization laws. Fixed ordinary callbacks with arbitrary
  captured records derive actual probe and stored-Mu cost correspondence.
  Full syntax now derives nonempty stored ordinary nodes and normalized union
  cardinality. Primitive empty-result and free-occurrence observations are exact.
  General Mu body/probe cost correspondence remains open.
  See `notes-gate-unfolding-rank.md`.
- Fresh-outer-dependent nested binder identity remains incomplete in general.
  Empty-child erasure now derives complete-record reuse. Every successful
  nested syntax execution replays exactly after cache growth. First execution
  still needs a closed-input no-pending theorem. Full nested traces now derive
  coherent caches, child provenance, edge residency, and issued-name history.
  A marked syntax fragment now proves first-run completion and complete
  payload coverage without assuming success. Further independent, erased-edge,
  and retained-reference classes also derive first-run completion. The last
  covers arbitrary depth with the same symbol at every binder. The combined
  grammar now composes retained ancestors with independent and erased-body
  subprograms inside pending contexts. Full-syntax pending-origin and identity
  footprint theorems derive the exact earlier reservation and old complete
  probes for any hypothetical alias. All syntax preserves pending slots and
  dense identity tables. A later resident old identity has the exact complete
  payload from before the pending interval. Recursive erased-edge construction
  now completes at arbitrary depth, including nested live children independent
  of the changed slot. Structural erasure now propagates through arbitrary
  node, union, and binder contexts. A mixed first-run theorem combines retained
  active frames with subprograms that read and erase enclosing inputs.
  Selective erasure of the immediate parent while retaining older ancestors
  now completes from actual source traces. Arbitrary ancestor subsets and
  computed empty-child erasure now includes arbitrary discarded constructor
  effects. Root unions, self-reference filtering, and consecutive retained
  binders have first-run completion proofs. General cleanup-induced erasure
  remains open. General absent-reference trace replay
  across changed nested local identities remains open.
  No source defect is known.
- Typed recursive join composition and public query laws are now proved.
  Full recursive support assembly, weighted flags, and absent-term errors
  now connect to those bodies. Diagnostic inspection and both sampler
  branches are also derived from local source records. Plain application now
  combines all views and derives its distinct source weight rules. Opaque external
  descriptors retain their own contracts.
  The construction-query repair blocks the reproduced payload mismatch.
  Arbitrary Haskell builders still need schema and key-discovery regularity.
- Full accepted ambiguous sparse Yes transport is proved through the actual
  identity quotient, including nested scopes, both guard polarities, Holds,
  and the current finite pruning loop. It establishes logical safety.
  No-refutation and successful compiler logical exactness are proved.
  Successful pruning retains all original backend-confirmed terms. Logical
  completeness of an original-edge fallback needs explicit backend adequacy.
  Logical planned-read transport for unrestricted ambient values now needs
  no exact backend spelling contract. General sort domains use an explicit
  compatibility condition for differing avoid lists. A sound
  callback can give sparse Yes and complete Unknown; exact backend language
  equality does not follow from logical safety.
  The all-Int solver adapter now derives the required soundness from returned
  calls and correct external responses. It preserves actual sort lowering
  and preflight Unknown. Arithmetic-core semantics agree with integerModel.
- Runtime interning, identity lifetime, containers, machine words,
  concurrency, lazy productivity, solver IO, PRNGs, and user codecs remain
  explicit correspondence contracts. There is no verified Haskell-to-Lean
  extraction.

Similarity minimization preserves representatives, not every original term.
Pool minimization starts a new uniform distribution over retained entries.
These contracts do not establish exact language or mass preservation.
Solver uncertainty and unsupported inputs are errors, not empty languages.

## Message board

Use `/home/tritlo/.agents/skills/msg-board/SKILL.md` and its bundled client.
Username: `mcfta-lean-review`.
Thread: `b4e17bb7-f021-446d-8e6f-9a3ded53eced`.
The board was read successfully after the network-restricted attempt failed.
Readback: `/tmp/mcfta-board-resume.json` (12 existing posts).

The current checkpoint post was **rejected by automatic approval review**.
It classified the branch/commit data and defect/proof details as a sensitive
export requiring payload-specific approval. No current post was sent.
The exact proposed payload is `/tmp/mcfta-board-proposed.json`. Matti answered
the approval question at 22:37 CEST: **"Keep the checkpoint local"**.
No approval is pending. Do not post this checkpoint or substitute an older
snapshot. Keep the prepared payload and all proof work local unless Matti
explicitly requests publication later.

## Next proof work

1. Preserve the proved all-Int solver-adapter connection, actual sort lowering,
   and conservative preflight Unknown. External responses and returned-call
   coverage remain explicit contracts. Keep restored backend-confirmed edges
   and logical validity separate. See `notes-source-read-integer-adapter.md`.
2. Preserve the complete typed family connections now proved for support,
   diagnostic inspection, both sampler branches, runtime flags, and missing
   terms. Arbitrary context-dependent Haskell builder schemas remain a
   separate source contract.
3. Complete the absent-reference replay argument for full nested syntax.
   Pending origins and complete old probe footprints are now derived without
   a syntax-fragment premise. See `notes-interned-pending-origins.md` and
   `notes-interned-node-footprint.md`.
4. Compose physical edit, require, leaf product, and projected union through
   their actual state transitions. Use finite completed-request replay.
   Preserve the derived raw-guard normalization phase and its strict rank.
   General nested equality fixed-point termination remains separate.
5. Extend the proved reachable-value unfolding rank to arbitrary nested Mu
   bodies. Unrelated deep cache entries are already permitted.
6. Keep runtime/source correspondence separate from executable Lean proofs.
   Update the coverage ledger and handoff at each validation checkpoint.

Address Matti in English and timestamp messages. Preserve unrelated work.
Do not add an ADR or update memory without a request. Keep theorem counts,
finite source checks, and implementation correspondence distinct.

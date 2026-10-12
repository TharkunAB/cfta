# microcfta formalization handoff

Updated: **2026-10-12 22:22 CEST (Europe/Stockholm)**.

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
No persistent goal exists. Do not create one without a user request.

## Repository and rebase

- Repository: `/home/tritlo/Code/mcfta`; Ubuntu/WSL2, Bash.
- Branch: `formalization/microcfta-resume-20261012`.
- Base: `origin/microcfta`, `de910ea` (merged findings fixes through PR #96).
- Latest proof integration checkpoint: `34fe917`.
- Other continuation commits: `3d3724f` (keyed families), `ee29250`
  (current equality), `840185a` (total substitution), and `d783309`
  (same-scope source repair and proofs).
- A documentation-only handoff commit follows these proof commits.
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
The new local source repair described below changes only
`microcfta/src/Data/CFTA/Refinement/Evaluate.hs`.

Do not replay the old source fixes over this base. In particular, upstream
changed total formula substitution, sparse nested-scope decisions, the
recursive equality gate, equality constraint interning, and top-level
self-reference removal from recursive unions.

## Verified checkpoints

- Existing Haskell suites on `de910ea` plus the new repair: **620 passing
  examples** (284 core, 194 generator, 142 refinement). Existing cases were
  extended; no new test file was added. Log:
  `/tmp/mcfta-scope-precedence-full.log`.
- Final integrated Lean build: **472 jobs; 26,011 theorem dependency checks**.
  All **469 proof modules** occur in the audit import closure.
  Log: `/tmp/mcfta-resume-final-audit.log`.
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
changed. The only new production change is the evaluator repair below. Do not rerun the whole Haskell suite
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

All delegated work is frozen and integrated. There are no remaining
untracked proof files or unfinished Lean errors.

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

## Remaining proof boundaries

- General termination of explicit equality/pruning fixed points on finite
  DAGs remains open. Finite language size is insufficient. The retained
  six-round example grows representation size.
- The new recursive equality gate can unfold an open unconstrained binder
  at the same path. A path-length argument alone does not prove termination.
- Fresh-outer-dependent nested binder identity is incomplete when
  normalization erases the dependency. The retained-reference and original
  independence cases are proved; no closed-input source defect is known.
- Typed recursive join composition and public query laws are now proved.
  Full recursive support/inspection assembly, weighted-dispatch flags, and
  the absent-term-field error branch still need connection to these bodies.
  Arbitrary Haskell builders can change schema between placeholder contexts.
- General accepted ambiguous sparse-to-complete query transport is open.
  The existing table alignment preserves identity flags and declarations;
  it cannot express the actual many-to-one quotient. A forward environment
  relation must preserve first-nonidentity lookup under both scope checks.
  Logical positive entailment and exact backend verdicts are different
  obligations. Timeout-limited Z3 has no assumed identification-stability law.
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
The exact proposed payload is `/tmp/mcfta-board-proposed.json`. An approval
question was sent at 22:22 CEST; its answer is pending. Do not retry without
that approval. The earlier handoff records approval only for the older
14-repair/613-example snapshot, not this larger current payload.

After approval, use the skill client, then read the thread back and verify
the new ID and text. A timeout is not publication. Name and link the skill
in the final answer if a post succeeds.

## Next proof work

1. Derive the accepted ambiguous-scope forward environment relation. The
   precise missing contracts are in `notes-substitution-policies.md`.
2. Compose full recursive support, inspection, weighted flags, and missing
   term-field error dispatch with the checked join bodies.
3. Handle nested binder key identity when normalization erases a fresh outer
   dependency. Retained dependencies and original independence are proved.
4. Establish source unfolding ranks and general explicit reduction fixed-point
   termination, or retain a concrete counterexample if one is found.
5. Keep runtime/source correspondence separate from executable Lean proofs.
   Update the coverage ledger and handoff at each validation checkpoint.

Address Matti in English and timestamp messages. Preserve unrelated work.
Do not add an ADR or update memory without a request. Keep theorem counts,
finite source checks, and implementation correspondence distinct.

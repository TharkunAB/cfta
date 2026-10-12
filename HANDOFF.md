# microcfta formalization handoff

Updated: **2026-10-12 12:17 CEST (Europe/Stockholm)**.

**Publication:** the user explicitly requested a push. The committed branch
through `b672913e85ca9bba9e751b2f7a788b9c35221562` was pushed to
`origin/spike/microcfta-lean-soundness` at 12:17 CEST. The rebased update used
an exact lease on `adb1f012b336ba0d1673f8fd7f310ad75bdfaf04`; that old remote
tip is retained in `backup/lean-before-rebase-20261010-1857`. A documentation
commit follows to record publication. All proof additions listed below
remain uncommitted and local. Do not mistake the pushed branch for a copy
of those files.

**Restart checkpoint:** the user requested completion of `HANDOFF.md` and
`FINDINGS.md`, then a restart. Proof work is frozen. The latest proof commit
is `bc6a978`. The following documentation commit does not include the
uncommitted proofs. Start with [FINDINGS.md](FINDINGS.md) and the next-work
list below. No source or proof edits are required to read this checkpoint.
After restart, keep this file current after each integration or validation checkpoint.

## Task and authorization

Matti requested a complete formal model of the intended constrained-language
library and a comparison with the implementation. The required properties are:

1. Compile equality- or liquid-constrained languages to an FTA with exactly
   their valid finite terms.
2. Prove enumeration sound and complete. Check that optimizations do not
   remove required expressions.
3. Give every distinct accepted FTA term one rank in `0 .. n-1`. Prove both
   decoder/inverse laws. Preserve the requested probability distribution.
4. Address efficient selection separately from a materialized reference
   enumeration. State actual algorithm and representation boundaries.
5. Model the library as it is. Record errors and fix source defects as found.

Latest instructions: "Keep pushing, we want full coverage. Be ambitious.
Only stop when you hit a hard wall." Source repairs are authorized. The latest
"Keep going" preserves this scope. The user requested this handoff because
of connection problems. At 10:39 the user requested these restart documents
and an end to this run. A later request to finish followed while the
documents were being completed.

Use `microcfta` as the base. The earlier `tidy/core-formula` instruction was
superseded after that PR merged. The user authorized this publication.
Future pushes and deployment still require a request. No persistent goal
was created. Do not create one without a user request.

## Workspace and Git

- Repository: `/home/tritlo/Code/mcfta`.
- Host: Ubuntu/WSL2, Bash. User timezone: Europe/Stockholm.
- Branch: `spike/microcfta-lean-soundness`.
- Last proof commit: `bc6a978e59d269544a65ce39e77ab650fdd795ee`.
- A documentation-only commit may follow it. Use `git log -3 --oneline` to
  read the current HEAD. The proof additions below remain uncommitted.
- Base: `origin/microcfta`, `bbeb7be4d331271ecd35ecd09ca661ac44ef7812`.
- Latest fetch/rebase: approximately 09:09–09:12 CEST today.
- Backup before that rebase: `backup/formalization-before-bbeb7be`.
- Another worktree exists at `/home/tritlo/Code/microecta/lean-fixes` on
  `fix/lean-findings`. Do not change it.

The latest base includes PR #89, single-pass equality reduction, and PR #90,
classified similarity and indexed minimization. About 180 local commits were
rebased successfully. Conflicts in `Minimize.hs` preserved all earlier safety
repairs. When installing a root representative, the indexed minimizer now
adds the root to each inserted child's parent set. Without that integration,
a later indexed copy can miss the inserted edge. This is part of the rebase
integration, not an eighteenth established public defect.

Recent local commits:

- `bc6a978`: exact associativity of grouped mass choices.
- `30f9da7`: keyed family fields and complete inverse queries.
- `b081d3f`: complete n-ary recursive inverse queries.
- `e24ebe5`: n-ary recursive record fields and finite sampler dispatch.
- `ad3804f`: classified similarity and indexed minimization schedules.
- `0227916`: adapt equality proofs to the new single-pass worker.

The initial `git pull --ff-only` was attempted. It could not fast-forward the
divergent proof branch. This was reported. Later fetching and rebasing were
authorized by the task. `.git` writes require sandbox escalation; the `git`
prefix is approved. Preserve unrelated files. Commit only known completed
files, not all untracked work.

## Current validation

Pinned Lean command:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
```

Latest aggregate success: **437 build jobs, 24,376 theorem dependency checks**.
Log: `/tmp/mcfta-grouped-merge-audit.log`.
This includes every committed module through `GroupedMergeAssociativity`.
It does not yet include the uncommitted keyed-n-ary, guard, or recursive-join
modules listed below. `Audit.lean` checks all imported project theorem
dependencies, including private/generated theorems. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. There are no admitted
project proofs or native-evaluation axioms in the audited closure.

Latest full Haskell suite after the rebase: **618 passing examples**:
282 core, 194 generator, 142 refinement. Log:
`/tmp/microcfta-bbeb7be-full.log`. The run finished around 09:16. No production
Haskell file has changed since. Do not rerun the whole suite without a new
source change or finding.

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
```

Use Nix for Haskell. The PATH addition is needed for the coherent linker/GMP
toolchain. Nix lock access requires approved escalation with prefix
`["nix-shell", "--run"]`. `fourmolu` ran on changed Haskell files.
`cabal-gild` has known pre-existing mismatches in unrelated
`microecta/microecta.cabal` and `microecta-generator/microecta-generator.cabal`.
No Cabal file was changed for this work.

Additional source comparisons passed:

- `/tmp/mcfta-nary-replay.hs`: 8 classes, 132 member inverses. Independent
  exact-rational recurrence with 9:1 atoms, a delayed branch, and a binary
  recursive constructor. Checks bounded/global PMFs and support acceptance.
- `/tmp/mcfta-keyed-replay.hs`: 8 classes, 254 inverses. Two recursive keys,
  four weighted operations, and two leaves. Checks normalized public key
  masses, conditional probabilities, and support acceptance.
- `/tmp/mcfta-keyed-nary-replay.hs`: adds a delayed third same-key leaf;
  8 classes and 285 inverses. The operator group's retained scale uses its
  source `totalCount = 4`. This scale matters relative to the delayed leaf.
- `/tmp/mcfta-single-pass-growth.log`: updated finite reduction reproduction.
  Public equality reduction is now one pass. Explicit `fixUnbounded` still
  needs six changing rounds on the nested fixture. Rows/nodes can grow.
- `/tmp/check-minimize-parent-index.py`: 94,560 single and 77,248 chained
  rewrite comparisons preserve ordered rows and parent completeness.

Temporary replay scripts are diagnostics, not new committed Haskell tests.
Their logs have the same stem and `.log` extension unless stated otherwise.

## Current uncommitted work and ownership

All paths below are under `lean/`. These files are intentional. Do not delete
them as unrelated work. All agents share the same filesystem.

**Root-owned, built, ready for integration:**

- `MicroCFTA/KeyedGuards.lean` — core keyed minimum/occurrence metadata;
  63-job build passed. This core syntax has no label constructor. Its
  combined term guard must NOT be applied to a label-erased value recipe as
  if that were the original source label metadata. The size guard survives
  erasure; the term-growth guard does not. See the active task below.
- `MicroCFTA/KeyedNaryQuery.lean` — 127-job build passed. Complete class and
  bounded/global preimages, ordering, and distinct positions against the
  independent `GroupedRecord.bounded` decoder.

**`/root/recursive_nary_body`: completed and frozen n-ary files:**

- `MicroCFTA/KeyedNaryAlignment.lean`
- `MicroCFTA/KeyedNaryMass.lean`
- `MicroCFTA/KeyedNarySource.lean`
- `MicroCFTA/KeyedNaryFields.lean`
- `MicroCFTA/KeyedNaryInverse.lean`
- `MicroCFTA/KeyedNaryCausality.lean`
- `MicroCFTA/KeyedNaryDispatch.lean`
- `MicroCFTA/KeyedNaryExamples.lean`
- `notes-keyed-nary.md`

`KeyedNaryExamples` passes a 138-job build. The source compilers use flat
mass-weighted `GroupedRecord.merge`; all four fields equal the lowering.
Full simultaneous source equations are derived from computed size guards.
Callbacks preserve false flags, order, and all preimages. The dispatcher
matches `mergeRecursiveGroups`: empty returns no group; singleton retains
the bare child; two or more use the flat choice. Raw `choiceRecursive` with
one branch instead adds `Choice 0`. Do not identify those two operations.
This keyed algebra models mass-weighted grouped choices. The single-root
`RecursiveNary*` algebra separately models count-weighted flat choices.

**Same agent, completed at 10:35:** `MicroCFTA/KeyedNaryGuards.lean` and
`notes-keyed-nary-guards.md`. The 114-job targeted build passed. The original
typed syntax maps labels to `OccurrenceGuard.Shape.constructor` and keeps
pay separate. The proof derives minimum and size-guard correspondence,
original term/used flags, exact public Boolean rejection, and the family
semantic guards from the combined public check. Direct flat-fold and
label/pay/singleton-choice examples are included. Both files are frozen.
They have not been added to the aggregate audit.

**`/root/static_dispatch`: recursive grouped-join work, frozen at 10:40:**

- `MicroCFTA/RecursiveJoinFields.lean`
- `MicroCFTA/RecursiveJoinCallbacks.lean`
- `MicroCFTA/RecursiveJoinLocal.lean`
- `MicroCFTA/RecursiveJoinTyped.lean`
- `MicroCFTA/RecursiveJoinExamples.lean`
- `notes-recursive-join-fields.md`
- `MicroCFTA/RecursiveJoinMass.lean` — new, separately built.
- `MicroCFTA/RecursiveJoinRecordBridge.lean` — incomplete; see below.

The five original join modules pass a 116-job build. An isolated audit
checks 9,166 transitive dependencies with only the three permitted axioms.
They model `recursiveChainTerms` / `recursiveJoin` with the actual `JoinN`,
`CenterKeyed`, `ArgKeyed`, and component tags. They prove all-arity selector
intervals, all-view inverse laws, false/true candidate bounds/order/distinctness,
local height correctness, and callback causality. The fused request fold
matches the source `scanl` prefix counts and `zip3` schedule. The typed
companion proves independent heterogeneous value/term index correspondence.
Kernel examples cover nullary and ternary joins, size splits, wrong keys,
malformed/short arity, all views, and heterogeneous `Bool`/`Nat` operands.

`RecursiveJoinMass.lean` passes a separate **129-job build**. It proves mass
convolution, complete ranked value/term projections, local-leaf validity,
and product-minimum/zero-mass-prefix laws. It is not yet included in the
isolated or aggregate audit, and the scope note does not yet cover it.

**`RecursiveJoinRecordBridge.lean` does not build.** The reported current
error is line 70: unknown theorem `List.sum_replicate`. The next step is to
try the existing theorem `List.sum_replicate_nat`, rebuild, and inspect any
remaining goal in `product_realizes`. This file connects grouped record
counts/decoders to the direct typed selector. Do not claim that connection
is complete. No proof is intentionally admitted. No further changes are
being made to it before restart.

These join modules are local adapters. Integration as a constructor in the
full typed mutual-family body remains to be assessed. Do not claim that the
ordinary `Apply` constructor already models private `JoinN` terms.

Both proof agents have reported their work frozen. Root is finishing only
the restart documents.
`conjunction_repair` errored due to a disconnected stream and has no pending
useful work. Fresh spawns and restarting some older threads fail with
"agent thread limit reached". Existing running/reusable threads work.
Use `collaboration.list_agents` and messages to verify state after reconnect.

## Next work

1. Confirm `git status`, read this handoff and `FINDINGS.md`, then resume
   the authorized formalization task. Preserve all uncommitted proof files.
2. Integrate the frozen keyed-n-ary files, add each module to `Audit.lean`,
   update `README`, `SYSTEM`, `COVERAGE`, and `API-COVERAGE`, run the aggregate
   build and dependency audit, then make a local checkpoint commit.
3. Integrate the completed original typed guard and recursive-join modules
   with their precise scope. Fix and finish `RecursiveJoinRecordBridge` before
   claiming its correspondence. Audit `RecursiveJoinMass`. Then continue
   missing whole-body join/family composition before declaring a hard wall.
4. The approved message-board post remains pending. It was deferred when
   the user requested the restart. Post the approved snapshot and verify it
   by reading back; do not claim that this already happened.
5. Recheck source inventory/import closure, documentation links, and
   `git diff --check` before a final result. The last full source inventory
   had 66 Haskell modules, all mapped in `API-COVERAGE.md`.
6. Keep source correctness, executable Lean models, and actual Haskell
   correspondence separate. A green suite or theorem count is not a full
   implementation-verification claim.

## Source repairs and important semantic distinctions

Seventeen source defects have been repaired on this branch:

1. Quantified application substitution could capture bound names.
2. Observed atomic 9:1 distributions could become 1:1.
3. Minimization could lose accepted root representatives.
4. Open recursive union could lose outer epsilon operands.
5. Pruning could unfold stored open binder bodies unsafely.
6. Grouped private alternatives could close differently from decoder terms.
7. Recursive support and terms lacked one consistent private boundary.
8. Grouped function spines could lose correlated children.
9. Ambiguous sparse actuals could incorrectly discharge guards.
10. Noncanonical conjunctions caused the reproduced finite reduction loop.
11. Independent semantic guard operands could share an incorrect scope.
12. Recursive equality narrowing could cross binder/path barriers.
13. Observed imports could omit explicit interned union alternatives.
14. Recursive observation filtering could discard recursive size fields.
15. Bounded construction could loop on retained binder cycles.
16. Self-dependent extracted measures could be accepted as exact values.
17. Open group positioning queried cardinalities to find recursive keys.

The new upstream parent-index integration is separately proved in
`MinimizeParentIndex`. `SimilarityWithin` proves exact ordered classified
pair scheduling and error behavior. Equality reduction proofs now model
the new public one-pass worker; explicit caller fixed points remain explicit.

General generator ranks count members/derivations. Different ranks can have
equal values and even equal constructor terms after labels erase private
choice structure. The FTA import path has the distinct-term bijection.
`RecursiveNaryExamples` checks this difference without treating it as a bug.

Similarity minimization deliberately keeps representatives. It does not
preserve every original term. Pool minimization also starts a new uniform
distribution over retained entries; it does not transfer discarded mass.
These weaker contracts cannot discharge the requested exact-language and
weight-preservation law. See `SYSTEM.md` and `notes-pool-minimization.md`.

## Remaining hard proof boundaries

- **General explicit equality fixed-point termination on finite DAGs.** The
  public worker is now one pass, but pruning and outer partial reduction use
  unbounded identity fixed points. A finite language is not a termination
  proof. The checked six-round fixture grows representation size. Earlier
  searches found no acyclic cycle; that is not a general proof.
- **Nested fresh-outer-dependent binder identity after normalization erases
  the dependency.** Retained fresh references separate pending keys. Original
  absence gives memo-key independence. Those results do not cover every
  erased-dependency nested callback. No closed-input collision or source
  divergence was established. See `notes-interned-fresh-probe-keys.md`.
- **Arbitrary nested runtime builder schemas.** Source builders are evaluated
  with index, mass, sampler, term, metadata, and support placeholders. The
  typed proofs preserve one constructor schema. Arbitrary Haskell inspection
  can change that schema, key set, or errors. Missing term callbacks remain
  a public error path, not an assumed total inverse.
- **Representation and external contracts.** Physical interning/hash maps,
  allocation identities, finite-word storage/lifetimes, concurrency, lazy
  productivity, solver IO, PRNGs, and user codecs/callbacks require explicit
  correspondence. There is no verified Haskell-to-Lean extraction.

Other remaining adapter gaps are recorded in `COVERAGE.md`. Do not declare
the whole implementation verified or hide an internal algorithm's desired
result in an assumed contract.

## Message board approval and pending action

Skill: `/home/tritlo/.agents/skills/msg-board/SKILL.md`.
Use its bundled `uv run --script .../scripts/board.py` client. Do not access
the live database file directly. Destination is `quack:tharkun:9494` unless
the configured URI overrides it. Use existing username `mcfta-lean-review`.
Thread: `b4e17bb7-f021-446d-8e6f-9a3ded53eced`.

An automatic review blocked the private checkpoint export at 05:16. At
approximately 10:30 the user explicitly answered **"Approve this project
checkpoint"** to the pending question to post **14 repairs, 613 passing
Haskell examples, checked Lean coverage, and remaining proof gaps**. This
clears that rejection for the approved checkpoint. The post has NOT yet
been sent. Do not claim it was published. That approved checkpoint is older
than the current 17-repair/618-example state; label it as the earlier snapshot
or keep the posted content within the exact approved checkpoint.

Last verified successful post before the rejection:
`70b407d6-3613-4906-a256-e3ee83ecd501` at about 04:40.
Readback: `/tmp/mcfta-board-checkpoint-0442.json`.
Other saved payload/readback files include `/tmp/mcfta-board-checkpoint-latest.json`
and `/tmp/mcfta-board-final.json`. Inspect their contents before use. A timeout
is not publication. Read back any new post and verify its ID and content.

## Working conventions

- Address Matti in English. Begin every user-facing message with the current
  `[YYYY-MM-DD HH:MM]` timestamp in Europe/Stockholm.
- Give material progress updates during long work. Do not ask permission
  again for authorized local work. The requested checkpoint push is complete;
  do not infer authorization to publish later proof work.
- User explicitly permits bounded parallel subagents. Preserve file ownership.
- Use `rg` first. Batch independent reads. Keep mutations and dependent builds
  sequential. Do not run blocking waits longer than 60 seconds.
- Haskell builds use Nix. New public Haskell declarations need Haddock.
  Do not add unrelated tests or Cabal formatting changes.
- No ADR was requested. Do not create one without asking.
- No memory update was requested. Do not write to memory files.
- Commit messages and PR text must not mention an assistant, model, or session.

Relevant memory was used earlier. A final answer for this work must end with
this exact memory citation block, after all ordinary prose:

```xml
<oai-mem-citation>
<citation_entries>
MEMORY.md:18-19|note=[separate completeness probability and optimization criteria]
rollout_summaries/2026-10-10T00-35-38-aDbb-formalize_microcfta_in_lean.md:17-18|note=[original machine checked formalization scope]
</citation_entries>
<rollout_ids>
01a1233c-a1c3-7940-98c0-126094feec91
</rollout_ids>
</oai-mem-citation>
```

If a board post is sent, name and link the msg-board skill in the final answer.
The previous board block need not be described as pending after the approved
post succeeds. A final answer should identify actual remaining hard walls,
state the verified results, and point to the coverage and findings documents.

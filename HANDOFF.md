# microcfta formalization restart handoff

Updated: **2026-10-13 04:16 CEST (Europe/Stockholm)**.

## Read first

The formalization is **not complete**. Matti requested this restart checkpoint
because the chat became unreliable. Continue the same full task. Do not replace
it with a smaller fragment, a theorem-count target, or a documentation task.
The latest proof checkpoint is **`d630667`**. Its complete audit passes:
**818 jobs; 33,080 theorem dependency checks**. All proof files from the parallel
work are committed and imported by `lean/MicroCFTA/Audit.lean`.

Read this file, root `FINDINGS.md`, and the linked notes before new proof work.
Root `FINDINGS.md` is the current report. `lean/FINDINGS.md` is historical.
Dated sections in detailed notes describe successive checkpoints; later results
can discharge an earlier section's stated gap. Use the theorem statements and
this handoff for current scope. `NEXT-PROMPT.md` contains the restart prompt.

## Full objective and authorization

The persistent user objective is:

> Keep going until you finish the formalization. Work around any issues you
> encounter, and note your fixes in FINDINGS.md.

The required properties remain:

1. Compile constrained languages to exactly their valid finite terms.
2. Prove enumeration sound and complete. Exact optimizations must retain all
   required terms and their weights.
3. Give every distinct accepted FTA term one rank and prove both inverse laws.
   Generator member multiplicity is a separate contract.
4. Prove requested probabilities. State algorithmic costs separately from a
   materialized reference enumeration.
5. Compare executable Lean definitions with the current Haskell implementation.
   State representation and external contracts explicitly.

Local proof work, focused source diagnostics, and necessary source repairs are
authorized. **Keep everything local. Do not push, deploy, or post to the board.**
Matti explicitly answered the previous publication question: **"Keep the
checkpoint local"**. No publication approval is pending. The prepared board
payload `/tmp/mcfta-board-proposed.json` must remain local.

Address Matti in English. Timestamp every response. He said: **"Don't give me a
breakdown, do the work. Keep doing it"**. Use short material updates and continue
working. Do not ask to continue work that is already authorized. Do not add an
ADR or update memory without a request. Preserve source correspondence and
honest proof boundaries; passing examples are not a general theorem.

## Repository state

- Repository: `/home/tritlo/Code/mcfta`; Ubuntu/WSL2; Bash.
- Branch: `formalization/microcfta-resume-20261012`.
- Correct implementation base: **`origin/microcfta`, `de910ea`**. This overrides
  older memory about `tidy/core-formula`.
- Latest proof commit: **`d630667`**. Earlier checkpoints: `5fffa19` (paired self
  filtering and binary projected progress), `9379798` (observed absence replay),
  `eb25dd9` (callback and cleanup emptiness).
- The next commit after `d630667` contains these refreshed restart documents.
  Use `git log -1` for its ID; a document cannot contain its own commit ID.
- Previous branch `spike/microcfta-lean-soundness` remains at `c2b1c0f`.
- Backup branch: `backup/lean-before-microcfta-20261012-2200`.
- Keep both retained stashes. The newest is `Preserve pending keyed nary and
  recursive join proofs before microcfta rebase`; its files were restored.
- Leave `/home/tritlo/Code/microecta/lean-fixes` on `fix/lean-findings` untouched.
- All proof workers were asked to freeze for this handoff. Do not assume an old
  worker or process is still running; inspect live state before relying on it.

The rebase replayed 175 proof/documentation commits. Old Haskell repairs were
retired because the base contains revised upstream fixes. Do not replay those
patches. The three current local production repairs are:

| Commit | Repair |
| --- | --- |
| `d783309` | Sparse substitution returns Unknown when removing an uncertain identity replacement could expose a later duplicate formal. |
| `14500e3` | Construction tokens reject payload queries inside unfinished recursive generator callbacks. Later proof work also repaired token removal on the finite return path. |
| `0333e7a` | Grouped discovery checks final keys and minima and returns InconsistentRecursiveFamily on disagreement. |

The current proof work made no further production Haskell changes. Root
`FINDINGS.md` rows 18–20 explain these repairs and their evidence.

Before new repository work, inspect status and refresh the correct remote base.
The continuation branch has no tracking branch. The previous successful command
was `git pull --ff-only origin microcfta`. If new upstream commits prevent a fast
forward, preserve the local checkpoint and rebase carefully; do not discard it.
Git writes need escalation in the current sandbox because `.git` is read-only.

## Commands and verified evidence

Pinned Lean: **4.34.1**.

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.InternedNestedProfiles
```

Latest complete audit: `/tmp/mcfta-restart-20261013-audit.log`.
It checks every imported theorem against the allowlist `propext`,
`Classical.choice`, and `Quot.sound`. It rejects omitted proofs, native evaluation
axioms, and custom axioms. The count is validation evidence, not a coverage
percentage. All 60 new Lean modules after `5fffa19` are integrated in `d630667`.

Use Nix for Haskell. Nix store/lock access needs escalation. Select the coherent
linker/GMP environment with the PATH prefix below.

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta /tmp/PROBE.hs'
```

All **620 existing examples** passed after the repairs: 284 core, 194 generator,
142 refinement. Full log: `/tmp/mcfta-construction-query-full.log`. After repair
20, generator and refinement suites passed again in
`/tmp/mcfta-family-discovery-validation.log`; core source was unchanged.
Fourmolu and Cabal-gild checks passed. No Cabal file changed. Do not repeat all
Haskell tests for proof-only work without a new reason.

Other retained evidence:

- `/tmp/mcfta-de910ea-focused.log`: formula, nested compile, recursive reduction,
  open union, and the 285-rank two-key recurrence.
- `/tmp/mcfta-heterogeneous-join-replay.log`: heterogeneous Bool/expression join,
  eight classes, 37 member inverses, exact masses and support acceptance.
- `/tmp/mcfta-runtime-bound-source-check.log`: 4,096 projected forests.
- `/tmp/mcfta-runtime-raw-orientation-source-check.log`: 1,156 raw leaf pairs.
- `/tmp/mcfta-projected-binary-progress.log`: exact public Haskell replay with
  nested endpoints and four changing binary-class passes.
- `/tmp/mcfta-projected-three-progress.log`: convergent three-peer example that
  refutes post-first-pass row retention beyond the binary case.
- `/tmp/mcfta-source-scc-nonassoc.log`: public Haskell confirms nonassociativity
  inside a mutually reachable narrowing component.

Files under `/tmp` are supporting diagnostics and can disappear. Committed
Lean counterexamples retain the critical mathematical obstructions. None of
these finite source probes proves extraction or universal source equivalence.

## Current nested-constructor result

Start with `InternedNestedProfiles`, `InternedStoredProbeTags`,
`InternedSpecialKeyCompletion`, and `InternedPendingProfileBoundary`.
All names in this document denote files under `lean/MicroCFTA/` unless qualified.

`InternedNestedProfiles.build_profile`, `closed_heap`, and `closed_profile`
cover **arbitrary full Syntax**, including nested smart/raw binders, actual
cache hits and misses, and pending outcomes. The root profile is either opaque
or a set of literal root references. Equivalence preserves opacity and reference
membership; it does not require equal list order. The source proof derives the
stored Mu decoder invariant from its actual two probes and fresh body call.
There is no binder-free restriction or assumed callback equation.

The supporting stack includes `InternedProfileSemantics`, `ProfileCallbackForm`,
`ProfileOrigins`, `TwoProbeProfiles`, `ProbeDecoder`, `ProfileEquivalence`,
`SyntaxProbeDecoder`, `ProfileHeap`, `ProfileRequest`, and the
`InternedRootProfile*` primitive bridges. The omitted `Interned` prefix in this
list applies to every name.

`InternedStoredMuOrigins`, `InternedNestedMuOrigins`, and
`InternedProfileMuOrigins` derive the actual original Syntax, captures, both
normalized probe calls, missing-key reservation, exact fresh body call, and
historical source/profile invariants for every complete stored Mu. This works
even when the containing closed execution returns pending.

`InternedStoredProbeTags` derives, for every such stored Mu:

- Body EmptyNode iff both actual probes are EmptyNode.
- Body equal to its own reserved reference iff probes are `(Depth, Unint 0)`.
- Smart cleanup returns EmptyNode exactly in those two key cases.

`InternedSpecialKeyCompletion.closed_safe`, `closed_no_empty_key`, and
`closed_no_self_key` exclude both corresponding pending keys for **unrestricted
closed Syntax**. This is a real first-execution result, with no syntax admission
or callback-law premise. `InternedProfileReferenceInputs` derives the required
literal-alias invariance. `InternedProfileTraceSites` obtains earlier completed
nested sites from the actual depth-body trace; `SpecialKeyReadiness` uses them.

**General no-pending remains open.** `InternedPendingProfileBoundary.closed_remaining`
reduces any remaining hypothetical encounter to two opaque probes, or two pure
probes with nonempty fixed captured root references. `InternedPendingOldCall`
also retains the active fresh ancestor reference and both exact probe records
already available before that ancestor reservation.

Exact local observed replay is available through ordinary constructors, root
unions, self filtering, and cleanup. Important modules: `InternedObservedAbsence`,
`OrdinaryAbsenceReplay`, `ObservedUnionReplay`, `ObservedCleanup`,
`BoundaryFreeAge`, `CallbackTransport`, `BoundaryTransport`, and
`LiteralObservations`. They handle actual common cache extensions, old Mu
payloads, and arbitrary target sentinel aliases. The full dynamic-Mu induction
must still derive its boundary-absence premises. A root profile drops ordinary
structure and Mu identities, so it cannot alone prove exact canonical replay.

Read:

- `lean/notes-interned-special-key-completion.md`
- `lean/notes-interned-stored-mu-origins.md`
- `lean/notes-interned-root-profile-source.md`
- `lean/notes-interned-profile-reflection.md`
- `lean/notes-interned-observed-root-replay.md`
- `lean/notes-interned-boundary-transport.md`
- `lean/notes-interned-literal-observations.md`

## Immediate next proof: complete free-name semantics

Three new support modules are complete and audited:
`InternedFreeNameDecoder`, `InternedFreeNameHeap`, and
`InternedFreeNameConstructors`. **The global free-name heap theorem is not yet
proved. The pure free-name interpreter has not been written.**

1. Define a full Syntax free-name interpreter. Use the existing root-profile
   interpreter for node empty-child decisions. Union combines free names.
   Both raw and smart binders remove the symbolic local; `cleanup_free` already
   proves exact free-field preservation.
2. Prove external-name map naturality and the fixed-captures/optional-argument
   form. Retain noninjective maps and captured probe aliases.
3. Prove the full source mutual induction and establish `FreeNameHeap` from
   empty caches. `Decoder.candidate_decoded` handles the three actual calls;
   `Heap.hit_free` handles canonical hits; `Constructors` gives actual node,
   union, and callback membership laws.
4. Use this with the existing origin and boundary lemmas for the remaining
   dynamic-Mu observed replay. It is support for general no-pending, not a
   substitute for that theorem. Pure nonempty-capture keys still need exact
   identity replay; opaque keys need the joint Mu-boundary argument.

The desired joint boundary fact relates an old smart unused-body result to
both earlier normalized probes. A temporary mirror search found no failure
in 275,563 closed terms and 1,358,140 active cutoffs (eight resource skips).
That is finite model evidence only. Do not promote it to an assumption.

## Equality fixed-point termination

The **complete physical projected-leaf schedule** is proved. Its bound is the
original occurrence weight plus one. It includes actual endpoint reads,
first-seeded target folds, recursive ancestor edits, required paths, class
order, empty propagation, and the final allocation-free fixed point in the
actual runtime cache. Endpoints must be leaf domains; ancestors can be nested.
See `EqualityLeafProjectionRuntimeBound` and
`lean/notes-equality-leaf-runtime-bound.md`.

The cache composition gap was repaired with raw leaf pullback and trimming of
dead occurrences. Never execute the next runtime step from a proof-prepared
cache. Source comparison also repaired the model's missing ordinary-node
operand orientation and changed the path worker to the exact source ordinary
union branch. These were proof-model repairs, not new Haskell defects.

For one fixed **binary projected class**, `EqualityFixedProjectionInvariant`
proves every original occurrence retains rows after the first reciprocal pass.
`EqualityFixedProjectionTermination.run_bounded` uses missing occurrence-row
pairs in a finite complete inventory. Nested endpoint rows are allowed. The
static row relation must be commutative and admit diagonals. The physical
adapter, original occurrence tracking, disappearing ancestor phase, and raw
normalization still need composition. See `lean/notes-equality-projected-binary.md`.

The binary invariant is false for three peers. `EqualityFixedMultiplePeers`
retains the convergent source-shaped witness and a separate abstract Steiner
cycle. The latter is not a source cycle. `EqualityFixedDegreeCounterexample`
retains the source-realizable five-degree table and nonassociativity inside a
mutual-narrowing component. An SCC cannot simply be treated as a semilattice.

`EqualityFixedRowProfile` proves local Boolean row modes after higher profiles
agree. `EqualityFixedProfileMaximum.highest_varies/prime_exists` derives a
removable maximum for one finite powerset layer over a strict-ranked row base.
**Neither theorem supplies arbitrary nested lifting.** A promising remaining
route is synchronized higher-profile induction. Generic commutative/idempotent
laws, semantic language finiteness, or a per-target rank are insufficient.
General fixed schedules with nested endpoints, three-or-more-path classes,
and interacting classes remain open. Prefixes can occur across distinct classes.

## Recursive gate rank and failed generalizations

`InternedPureProbeGate` and `InternedProbeOpacity` derive actual stored-body
unfolding completion and strict head-rank decrease when the depth probe is pure.
The other probe is then pure, its level is zero, and the actual body depth is
zero. This covers unrestricted source syntax, with source-derived premises.
The remaining general case has opaque probes. Earlier shallow, reachable-only,
closed-nested, and marker one-step theorems retain their scopes.

Do not retry these disproved shortcuts:

- `InternedOldBodyProbeAliases`: an unused old body need not equal either probe.
  Captured depth and ordinary sentinels can be filtered differently.
- `InternedNestedProbeCostBoundary` and `InternedClosedProbeCostBoundary`:
  exact free-occurrence cost coverage fails in a complete closed source-model
  cache (slot 19). The body has sentinel costs 1; both probes have costs 0.
  The closed program completes EmptyNode. Keep `FlatProbeHeap` restricted.
- `InternedSourceRankStutter`: staged scoped source-model calls with explicit
  `Depth`/`Unint 2` captures and cache prepopulation give a real modeled unfold
  with both candidate ranks `2 -> 2`. Later ranks are `[2,2,1,0]`. This is not
  divergence. It is not yet a closed empty-environment reachability theorem.
  Haskell confirmation and universal callback-law admissibility were not
  established at this checkpoint.
- Exact ordered root-profile equality is false. Reversed capture order can
  hit an earlier Mu pair and return the first canonical union order. The
  corrected `/tmp/mcfta-profile-order.lean` check passes; set-based `Equivalent`
  remains valid.

The open cost fixture `/tmp/mcfta-cost-probe-masked-alias.hs` also confirms both
actual-own-to-probe substitution equations in Haskell. That does not establish
the documentation's stronger equation for every captured/supplied name pair.
See the chronological `lean/notes-gate-unfolding-rank.md`.

## Preserve other completed work and remaining contracts

Typed keyed n-ary and nested heterogeneous recursive-join proofs are complete
under their stated local leaf contracts. They connect support, diagnostics,
samplers, masses, flags, inverse queries, rank ordering, and original guard
metadata. `RecursiveCompleteRecord` assembles those fields. Keep generator
members distinct from unique accepted FTA terms. Opaque Haskell builder schema,
key-discovery, codec, and productivity contracts remain explicit.

Sparse Yes now transports to complete logical satisfaction. Current pruning
and successful compiler classification inherit logical soundness and exactness
on their success domain. Backend-confirmed language equality needs backend
adequacy: a sound name-sensitive callback can give sparse Yes and complete
Unknown. The all-Int solver adapter derives its laws from correct returned
external responses. See `lean/notes-source-read-logical.md` and
`lean/notes-source-read-integer-adapter.md`.

Runtime identity lifetimes, machine words, host containers, concurrency, lazy
productivity, solver IO, PRNGs, and user codecs retain explicit correspondence
contracts. There is no verified Haskell extraction. Similarity minimization
preserves representatives; pool minimization starts a new uniform distribution.
Neither is an exact term/mass-preserving optimization under the stronger contract.

Use `lean/SYSTEM.md`, `lean/COVERAGE.md`, and `lean/API-COVERAGE.md` for the wider
ledger. All 66 Haskell modules occur in the API inventory. Keep theorem coverage,
source diagnostics, algorithmic costs, and external assumptions separate.

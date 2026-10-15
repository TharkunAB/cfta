# Endpoint recursion guard and preserved source models

## Main 24a710a3: endpoint recursion guard

Current source main: `24a710a39e5adcc94c4d986f0bda81a8483bdba8`.
Preserving merge: `6a02619c`. Proof checkpoint: `3eed507c`.
Pre-merge checkpoint: `f976cb6a`. Backup:
`backup/formalize-before-main-24a710a3-20261015-1612`.
Continue on `formalize` and push verified checkpoints. Read
`lean/notes-main-24a710a3.md`, then `lean/notes-native-field-running-invariants.md`.
After a pull, check fetched main ancestry before proof edits. Keep all earlier
proofs, repros, repairs, drafts, stashes, and worktrees. Full scope remains open.

This main update changes the existing equality gate. An ordinary path endpoint
now blocks a class if it reaches a constrained Mu. The helper checks cached
zero depth first, traverses ordinary children and stored union members, and
stops at every Mu. The path gate still blocks references and unions before
its own finite shortcut. The helper has a new global unary memo. The comment
conflict retained the upstream explanation and the standalone repro pointer.
All production definitions now match main. Only that pointer and the earlier
constructor-probe changelog entry differ in the four package trees. Interned
construction, intersection, equality normalization, and Sized are unchanged.

Six additive Lean modules model the stronger policy. SourceEndpointReachability
has a structurally total stored-record traversal and an exact witness theorem.
EndpointRecursionGate preserves dispatch order, completed-result stability,
selected-class subset of the previous policy at the same fuel, and the bounded
constrained-pass law under existing primitive graph laws. EndpointGateCompletion
proves ranked total decisions, finite completion, and agreement for nodes,
paths, and classes. SourceEndpointGate and SourceEndpointGateCompletion use
actual certified source records and the proved unfolding rank. Original source
construction derives finite current-policy checks for every finite path.
SourceEndpointCallerRegression evaluates the preserved original constructor
input and proves that its first endpoint is closed and has the new witness.
Every certified readback changes from the old clear answer to the new barrier.

The old ConstrainedRecursionGate, stateful/memo gate families, selection pipeline,
and caller-cycle proofs remain byte-identical. Their endpoint policy is now
historical. Their theorems remain valid for their definitions. They do not
prove exact current-source selection or cache effects. The new results do not
retarget those workers or model the new global memo. The generic pass law is
conditional on primitive operations; it is not a proof of the native caller.

The preserved Haskell caller repro with --cold now completes with Just 17.
Its unchanged default certificate prints Just False and raises its deliberate
certificate error: the repaired gate no longer produces the old narrowed-child
cycle. This is an expected historical-certificate mismatch. The upstream test
passes for reducePartially, termsMatching, and the README fixpoint composition.
The specific source cycle is fixed. General one-pass and repeated-pass
termination remain open. Unequal path lengths can still move constraints
below an unconstrained recursive unfolding. Do not infer a new cycle without
an actual current-policy witness.

Next carry the current policy through actual stateful selection and both older
gate memo families. Model the new descendant memo and its ordered recursive
calls. Boolean agreement alone does not imply equal caches. Then reconnect
class folds, guarded native prefixes, and the recursive caller. The existing
native intersection bodies are unchanged: continue deriving InputsThrough,
semantic finish receipts, internal ranges, sidecar allocation coverage, and
the candidate-parametric Mu/repeated-pair context law. New derived-refinement
frontends, named measures, global causal prehistory, pending equality thunks,
container/hash/word adequacy, lifetime capacity, unsafe IO, GHC, general
completion, repeated fixed points, getAllAtPath, decision-model, parser/decoder
bridges, and extraction remain open. Keep older constructor/equality work.
Sized exact classes, finite execution, canonical sequence, distinct size order,
and both signed inverse implications remain separate contracts.

The strict Nix build passes all libraries, executables, tests, and benchmarks.
All six suites pass: 697 examples plus the golden suite. Fourmolu passes both
changed Haskell files. Cabal metadata and Sized are unchanged; their previous
checks and separate 205-rank probe were not repeated. The Lean audit passes
1,981 jobs and 50,858 dependency checks with only permitted axioms. No new
warning occurs; the old unused-input warning remains. Validation logs use
`/tmp/mcfta-main-24a710a3-{tests,build-format,lean-audit}-20261015.log`.
The caller observations have separate caller-cold and caller-old-certificate
logs with the same prefix. Component checks do not establish full scope.

The previous snapshot `/tmp/mcfta-main-6fe34ab8-checkpoint-20261015-1605/`
retains all 2,629 file hashes and its clean f976cb6a checkpoint. The new snapshot
is `/tmp/mcfta-main-24a710a3-checkpoint-20261015-1625/` (2,636 files).
All prior Lean definitions except additive Audit imports, old repros, marked
drafts, stashes, other worktrees, and external draft/limit files remain.
Only Equality/Operations changes among the previously preserved optimized
interned/equality/Sized source files, by the reviewed upstream guard and a
comment pointer. Weekly allowance was 91% at 2026-10-15 16:23 CEST. Refresh
before work; stop work and owned workers at 1% or less. No board posts or
deployments. Older source heads, counts, and next targets below are historical.

## Source checks and exact limits

The path gate returns true for references and stored unions before the finite
shortcut. The helper first checks zero nested depth. A zero-depth stored union
therefore has helper answer false and path-gate answer true. These branches
are distinct. A free ordinary endpoint short-circuits before the helper call.
A helper call reaches its global memo before its body checks depth. The new
pure helper proves the Boolean computation, not this memo trace.

Witness follows only stored ordinary children and union members whose cached
depth is nonzero. At a Mu it requires the supplied unconstrained read to be
false. SourceMemoGate.unconstrained supplies the actual visited-node source
predicate, which checks full constraints, including residual guards. The
witness does not establish independent language semantics for an arbitrary
predicate or incorrect metadata. The certified source adapter reuses existing
metadata, construction, unfolding, and immutable-record invariants.

The old ancestor-cycle source proof remains imported in Audit. The new
SourceEndpointCallerRegression imports that exact original syntax and evaluates
only original construction and the current helper. Its certified_endpoint law
states the old false and current true answers for every certified readback of
the observed ordinary endpoint. It does not execute a whole pass. The Haskell
regression supplies finite runtime evidence for the repaired pass behavior.

The upstream test retains the equality class and the original root. It does
not replace the root with EmptyNode. Enumeration and accepts check the retained
constraint. The generic pass theorem preserves the full original local and
inherited equality conditions under Laws. It does not establish all Laws for
the current physical operations or prove an outer caller decreasing measure.

Read-only source audits:
`/tmp/mcfta-main-24a710a3-gate-audit-20261015.md` and
`/tmp/mcfta-main-24a710a3-caller-audit-20261015.md`.
Completion validation:
`/tmp/mcfta-endpoint-gate-completion-20261015.md`.
Additional focused logs:
`/tmp/mcfta-endpoint-{gate-comparison,source-adapter,caller-regression}-20261015.log`.

## Reproduce the preserved source observations

Use the project Nix shell and the exact package unit:

```sh
nix-shell --run 'env PATH=/usr/bin:$PATH cabal exec -- runghc --ghc-arg=-package-id --ghc-arg=cfta-0.1.0.0-inplace lean/repro/OuterCallerCycle.hs --cold'
```

The observed output is Just 17. Omit --cold to run the unchanged historical
certificate. Its observed output is Just False followed by its deliberate
outer caller cycle certificate error. That command exits with failure because
the earlier narrowed-child assertion is false on the repaired source.
Do not change the retained repro to conceal the policy difference.

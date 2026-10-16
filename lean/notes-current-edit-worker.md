# Current proof state and literal checked class execution

Updated: 2026-10-16. Source main is `ccebf0f7`. The preceding published
checkpoint is `67f2b5d0`. Proof commits are `87ad619b`, `2cbebf92`, `2f1af1cf`,
and `ca2fe823`. Root FINDINGS.md keeps the external Haskell fix registry first.
This increment changes no Haskell implementation or test.

## Top-level objective

Prove that the current Haskell library implements its specified constrained
tree languages and generators on each supported input domain. Prove finite
execution where the API promises it. State solver, callback, codec, machine,
and host assumptions explicitly. No completed theorem verifies the whole
Haskell library.

The exact query contract includes distinct accepted terms at each node-count
size, finite size-class evaluation, exact counts, size-major enumeration, and
both rank/unrank inverses. Sampling has a separate distribution contract.
Accepted terms, accepting runs, and generator members can have different
multiplicities. Exact transformations preserve the language. Merge and other
over-approximations have inclusion contracts. Representative selection can
remove terms. Preserve the original sorted explicit rows where rank matters.

## Strongest existing capstones

SourceSizedApiLaws.Exact states the modeled public Sized laws. The finite-key
modules derive these laws from validated original row maps under the stated
guard contracts. Concrete host execution and the broader generator adapters
remain separate obligations.

SourceCurrentAllocatedPartialActual.root_exact proves exact independent
language preservation and the full returned physical and memo invariant for
a supplied completed recursive reduction call. Initial Context, resident
input, ready allocated empty inherited constraints, source-aligned Reads, and
reached checks remain explicit. This theorem does not establish completion
of arbitrary constrained calls. The public reducePartially performs one pass.

## New literal workers

Nine additive modules extend the current allocated merge, Target, and shared
Force/Leaf workers:

- SharedTargetWorkerStability proves unconditional successful force/leaf
  stability and whole-state uniqueness under different stage bounds.
- SharedEditWorker implements EditNode, Children, Rows, and List. Its six
  bounds control edit recursion, projection, reads, merge, selection, and
  native execution. Failures retain the exact reached checked state, local
  slots, merge memo, and diagnostic. Head exposure retains pending,
  unresolved, and exhausted outcomes. Unselected children retain their
  values. Raw row reconstruction retains the full original constraint.
- SharedEditWorkerCompletion derives stable sufficient bounds from finite
  current edit graphs. SharedEditWorkerStability proves unconditional
  success stability and whole SharedState uniqueness. Actual derives finite
  graphs, Reads, physical receipts, and probe heaps from initial selected
  support. Supplied successful returns receive these facts at their exact
  output and state. list_language derives narrowing and preservation of
  class-satisfying selected terms.
- ClassWorker runs compiled edits with empty class-local slots over the
  supplied full checked state and warm merge table. The right fold executes
  the tail before the head captures its returned forest. Final propagation
  follows only a successful full fold. Failure retains all reached slots.
- ClassWorkerCompletion derives stable six-stage bounds from finite classes
  and passes. ClassWorkerStability proves unconditional success stability
  and exact forest, Checked, and merge-table uniqueness.
- ClassWorkerActual.caller_finite constructs stable literal pass execution
  and a full caller Post at the computed next inventory. Its initial domain
  includes Context, resident values, coherent nontrivial records, selected
  path domains, and actual-prefix ranges. Both outer result families and the
  fourth memo remain valid. The result narrows the input language. Membership
  agrees with the input for forests that satisfy every class. caller gives
  the same result at a supplied successful return. No future body law is a
  public premise.

The finite endpoints construct logical global-query read receipts. These
literal workers do not execute concrete host global-query tables. Serial
models do not prove GHC forcing, lazy publication, or the noConstraint CAF.

## Remaining work

1. Implement literal dynamic conjunction rows and worklists, its decision and
   fourth-memo wrapper, Scan, local reduction, parent construction, and the
   mutual outer worker. Connect the same actual execution to root_exact.
   Read conjunction-worker-next.md in this checkpoint's evidence directory.
2. Prove general constrained outer termination on a justified domain.
   Unequal-length path classes can move constrained structure deeper. Local
   finite completion does not provide a decreasing outer measure. Repeated
   pass convergence is a separate obligation.
3. Complete current frontend adapters for root typing inputs, Binders, type
   domains, deriveLTAOn, GHC pruning, LTA contracts, codecs, and generator
   ranks. Retain separate exact Sized and probability contracts.
4. Connect the models to concrete Haskell containers, heap forcing, pending
   publication, global query tables, identity lifetime, concurrency, machine
   bounds, external solver IO, random draws, callbacks, and codecs.
5. Compose construction, graph readback, transformations, exact queries,
   generation, and sampling under their actual common domains. Preserve the
   optimized interned core and the older constructor and equality targets.

## Validation and repair handoff

Pinned Lean 4.34.1 passes the full Audit: 2434 jobs and 57891 theorem dependency
checks. Only propext, Classical.choice, and Quot.sound are permitted. The old
unused-input warning remains. Public signatures, dependency probes,
integration kernels, independent reviews, frozen sources, and preservation
evidence are in lean/restart-evidence/20261016-current-edit-worker/.

No Haskell implementation or test changes occur. Reuse the preceding strict
Nix build, 788 examples plus golden, 15-file Fourmolu, and four-package
Cabal-gild and metadata checks. Record every later Haskell fix FIRST in root
FINDINGS.md with failure, reproducer, files, commit, checks, and upstream
status. Preserve all older proofs, counterexamples, repairs, and drafts.
This is progress toward the full-library objective.

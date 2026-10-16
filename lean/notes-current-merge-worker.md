# Current proof state and literal merge execution

Updated: 2026-10-16. Current source main is `ccebf0f7`, merged into
`formalize` at `44ba7bf1`. The last published checkpoint before this work
is `10b58c54`. Proof commits are `03c50a7d`, `cb2f4061`, and `03b48a40`.
Root FINDINGS.md keeps the Haskell repair registry first.

## Full proof objective

The objective is correspondence between the specified constrained tree
languages and generators and the current Haskell library. For each supported
input, public operations must satisfy their stated semantics. Operations
that promise finite results must terminate on their stated input domain.
Solver, callback, codec, and host assumptions must remain explicit.

The exact query contract has separate obligations: finite evaluation of each
node-count size class, exactly the distinct accepted terms, exact counts,
size-major enumeration, and both rank/unrank inverse laws. Generator runs
and distinct terms have different multiplicities. Sampling must use the
specified distribution over the correct members.

Each transformation has its own contract. Exact transformations preserve
the language. Over-approximations retain the input language and can add terms.
Representative selection can remove terms. Language equality does not imply
the same rank order. Exact queries use the original sorted explicit graph
rows, as specified in docs/adr/0004-explicit-graph-boundary.md.

There is no single completed theorem that verifies the whole Haskell library.
The present result consists of proved component specifications, source-level
operational models, composition theorems, and explicit remaining adapters.

## Strongest current results

SourceSizedApiLaws.Exact states finite class evaluation, distinctness, exact
membership, counts, signed query errors, both rank inverses, and ordered
prefixes. SourceSizedFiniteKeysPublic.native_sized_exact derives this record
for successful modeled dispatch on a validated original finite row map.
Finite keys come from that map. Relevant guard and solver contracts remain
explicit. Concrete host evaluation remains a separate correspondence.

SourceCurrentAllocatedPartialActual.root_exact proves language equality for
a supplied completed current recursive reduction call. It retains the exact
returned physical state and memo invariants. Its premises include legitimate
initial Context, available input, ready allocated empty inherited payload,
strict source-aligned Reads, and reached machine checks. The eight mutual
call families derive their own result laws from smaller actual calls. This
does not construct arbitrary completed calls or prove general termination.

Constructor, native intersection, required-path, class-pass, query memo,
generator, rank, and probability modules supply further component results.
Their scope remains the stated source domain. A green Audit is evidence that
the included proofs check. It is not whole-library correspondence.

## New literal allocated merge worker

Five additive modules form this checkpoint:

- SourceCurrentAllocatedMergeWorker interprets the current allocated Code.
  Every success and failure retains the actual heap, equality operations,
  and merge memo. Top rows allocate their empty field at the reached state.
  Work fuel and selection fuel are separate. A positive-work ready hit needs
  no body fuel. A failed stage does not execute its continuation.
- SourceCurrentAllocatedMergeWorkerSound maps each successful execution to
  the same Run or Call, with identical output and complete allocated state.
- SourceCurrentAllocatedMergeWorkerCompletion derives stable sufficient
  bounds from finite Run and Call graphs. Every larger pair of bounds gives
  the identical return. It also proves success stability and both graph
  equivalences. It does not select an implementation by existential choice.
- SourceCurrentAllocatedMergeWorkerActual.finite constructs a finite Call
  from legitimate warm Context and input availability. It derives stable
  literal execution, the full caller Post, output availability, conditional
  closedness, and input-language inclusion. It preserves both outer result
  families, native tables, the domain cache, and the fourth memo. Merge is an
  over-approximation. Its result is not claimed to have equal language.
- SourceCurrentCurriedDefaulting models the current four-branch narrowHeads.
  Leaf `?any` has first priority. The old filter agrees only when `?any` is
  absent. An actual constructed two-row example refutes unrestricted transfer
  of the historical no-open law. This is a proof adapter gap, not a verified
  Haskell defect.

The merge capstone constructs logical global-query read receipts. The literal
worker does not execute concrete host global-query tables. Serial execution
does not prove GHC demand order, lazy publication, or the noConstraint CAF.

## Remaining areas

1. Compose literal executable workers for checked Target, Force/Leaf, edits,
   Class/Pass, conjunction, Scan, local reduction, parent construction, and
   the full outer two-family caller. Their strongest current endpoints are
   relations and receipts. Preserve exact unsuccessful states and source
   reads. Then apply the proved mutual theorem to the same actual execution.
2. Prove general constrained outer termination on a justified domain.
   Unequal-length path classes can move constrained structure deeper.
   Language narrowing and finite local steps do not supply a decreasing
   recursive measure. Repeated-pass convergence is separate; the public
   reducePartially operation performs one pass.
3. Complete current frontend adapters. The refresh adds root typing inputs,
   Binders, type domains, and deriveLTAOn. Existing empty-input Nesting and
   historical defaulting proofs do not cover those full APIs. Binders can
   give a finite cyclic graph with an infinite term language. GHC instance
   pruning, bounded domain unrolling, LTA contracts, codecs, and generator
   run/rank correspondence need their own proofs. See frontend-proof-coverage.md
   in the evidence directory.
4. Connect operational models to concrete Haskell containers, lazy heap
   forcing, pending memo publication, identity lifetime, concurrency, and
   machine bounds. Connect external solver IO, random draws, callbacks, and
   codecs to their explicit contracts. Older constructor and equality work
   remains active beside the optimized interned core.
5. Finish full pipeline composition across construction, graph readback,
   transformations, exact queries, generators, and sampling. Preserve original
   row order where rank matters. Distinguish accepted terms from accepting
   runs and generated values throughout the composition.

## Source refresh, validation, and handoff

The upstream delta has 20 files in cfta-generator and cfta-ghc. It changes
no cfta core or Sized source. No local Haskell behavior or test change is
added. Existing repair details and upstream status remain in root FINDINGS.md.
Record every later Haskell repair there with its failure, reproducer, files,
commit, checks, and upstream status.

Pinned Lean 4.34.1 passes the full Audit: 2417 jobs and 57607 theorem dependency
checks. Only the three permitted foundations and the old unused-input warning
remain. The strict Nix all-component build passes. All six existing suites
pass: 788 examples plus the hole-fit golden check. Fifteen changed Haskell
files pass Fourmolu. All four active packages pass Cabal-gild and metadata
checks. The first GMP linker failure was an environment path issue; the
documented host PATH fixes it without a source change.

Raw validation, independent reviews, public theorem probes, integration
kernels, source copies, hashes, and preservation evidence are retained in
lean/restart-evidence/20261016-typing-refresh-merge-worker/. Read
target-current-next.md there for the next dependency order. Keep the full
goal active. Preserve every older proof, counterexample, repair, and draft.

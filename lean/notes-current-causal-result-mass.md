# Current library proof status and causal generated payload bounds

This checkpoint starts at published 1a8e5b7b. Its proof commits are 2f7a3bc1,
aa3cb202, 33387176, and 5166ffde. Source main remains c0cc8a05, merged locally
at 896b0a1c. The full library goal remains active.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target theorems. The complete implementation theorem
does not exist yet. Support must describe initial inputs and resources.
It must not assume future successful execution or the desired result.
Documented errors and validation order are observable results.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Distinct terms, accepting
runs, and generated members remain separate. Exact transformations require
language equality. Over-approximations require inclusion. Representative
selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact size classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys supply a finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction with Mu and unions. Initial syntax bounds allocations. Initial captures and stores now bound complete returned and stored payload structure for every outcome. | Haskell lazy publication, interning, and runtime correspondence. |
| Checked recursive intersection | Initial numeric bounds construct finite exact queries. Current inventories and captured origins retain joint laws for produced operands. | One initial resource budget for complete query sequences that consume new results. |
| Original-source serial queries | One initial budget constructs any finite list of queries over a fixed original source. Warm native caches, equality operations, and global tables remain present. | New operands outside that source and total memory capacity. |
| Generated optional-binder series | One computed initial source bound constructs actual result-fed optional binders and their checked physical trace. Numeric payload and allocation budgets compose across the entire series. Native tables, domains, and equality operations retain their exact initial values. | Other recursive-query instructions and full generated-query budgets. |
| Memo-aware Merge and selected Operand | Actual Merge derives universal cap certificates before publication. Initial selected domains construct finite Operands with unrelated open ordinary siblings. | Arbitrary constrained Mu bodies and runtime publication. |
| Mixed Edit and class pass | Actual editor reads and the tail-first class pass retain stores and derive finite syntax depth bounds. | General first target misses and editor/class completion from initial resources. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | This ordinary domain excludes Mu, references, and unions in every descendant. |
| Other components | Existing language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted driver proofs remain preserved. | General constrained descent, convergence, current adapters, and complete public pipelines. |

These results concern explicit modeled source workers and caches. They do
not establish full correspondence with compiled Haskell execution. A theorem
count or successful check does not give a completion percentage.

## Causal structural payload bounds

InternedValueMass counts value, edge, and list constructors. It includes the
complete Mu body and both stored probes. It ignores identities, keys, cached
depth, free-name metadata, symbols, and guards. Explicit caller SizeOf
instances give a separate upper bound. Mass is not a byte or runtime count.

InternedValueMassHeap.Stored bounds every actual completed node and edge
payload. Its computed initialBound sums successful reads from the two
independent original issued ranges and adds one. Facts derives this initial
store bound. Available values and resident edges inherit it. Cache
reservation changes no complete payload map. Insertion accounts for the
actual earlier first-writer winner and the new candidate.

The primitive proofs retain this store through literal node, edge, and union
construction. Weighted canonicalization, flattening, and deduplication
cannot increase the charged list mass. Source self-reference filtering
retains the same bound. Smart cleanup cannot increase value mass.

InternedFreshOrdinaryResultMass transforms the initial store and captured
value bound through the full actual constructor schedule. It covers every
stopping outcome. A successful result inherits the same transformed bound.
The proof needs no Facts, availability, closedness, fragment, callback result,
or successful execution premise. Nested Mu and unions remain supported.
Each binder accounts for all three possible body evaluations, normalized
probes, reservation, candidate publication, and actual stored readback.

## Numeric bounds from the initial body mass

Stored encoding has node and edge charge bounds of `2 * 3^mass`, with two
units of slack. Every literal encoded row, union-member, and child-list width
is bounded by that same initial mass. Closed constants can use the opaque
input shortcut. Open nested Mu uses the full encoded binder schedule.

The uniform transformer repeats the conservative growth rule:

`grow(width, bound) = (width + 3) * (bound + 1)`.

The original node and edge constructor budgets bound the number of growth
steps. This dominates the full ordered syntax transformer. It does not
depend on a future returned body. MassBudget therefore derives a numeric
optional-binder charge and returned-store bound from one initial number B:

`charge(B) = 6 * 3^B`

`ceiling(B) = evolve(B, 12 * 3^B + 4, B)`.

These bounds are conservative logical bounds. They do not establish useful
concrete host headroom or total memory capacity.

## Serial generated results and actual checked execution

MassSeries.run passes the literal returned value and heap to the next actual
maybeMu. massAfter and credit depend only on the initial bound and the
number of keys. They determine all later payload bounds and accumulated
constructor charges. Their addition laws use the exact numeric common bound.

run_bound covers every stopping outcome, including pending prefixes. It
retains Facts, availability of completed results, record growth, and issued
history. Initial Context, decoded depth heap, and Covered construct a
successful complete series. complete applies the one original computed
source bound to that same execution. It takes no later-entry counters,
future WordRanges, supplied complete execution, or desired result law.

MassCheckedSeries constructs the literal optionalBinder code and the actual
physical Trace of the same length. Each result feeds the next continuation.
The final checked state changes only the constructor heap. Both native memo
tables, domains, and equality operations remain exactly populated as before.
Initial Good and static field checks derive final Good on this same trace.

This sequence contains only optional binders. It does not prove the resource
bound for a complete recursive query or a general constrained caller.

## Remaining work

1. Lift the initial mass and allocation producer through all actual checked
   query instructions. Cover native node and edge workers, Work requests,
   reads, projection, union expansion, domain allocation, and captured
   continuations. Compose complete serial queries that consume new results.
2. Construct general Target, Force misses, mixed Edit, and ClassPass from
   initial resources. Existing depth and store results prove preservation;
   their general finite execution remains separate.
3. Produce the active and stored certificates required by general constrained
   outer descent. Keep the source gate that accepts closed no-Mu endpoints
   independently of their own guard. Cover arbitrary constrained Mu bodies.
4. Prove repeated reduction convergence. Complete remaining recursive pruning
   and compiler callers. One complete pass is not a fixed point.
5. Complete current typing and refinement frontend adapters. Include drawn
   fields, symbolic measures, errors, validation order, and generator rank
   order. Complete solver, runtime, IO, randomness, concrete capacity, and
   user-code adapters with explicit assumptions.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

Preserve older constructor and equality work and the optimized interned core.
Do not repeat the completed source-rebase, origin, Merge, selected-Operand,
mixed-editor cap, full constructor mass, or serial optional-binder proofs.

## Validation and Haskell handoff

The pinned Lean 4.34.1 Audit passes 2864 jobs and 63784 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All ten production
modules pass strict checks with zero-byte final logs. All 134 imported axiom
and signature pairs pass in fifteen groups. Seven component manifests
verify 247 entries. Raw attempts remain
in restart-evidence/20261017-causal-result-mass. Read checkpoint-validation
for imported signatures, constructive kernels, component manifests, and hashes.

Preservation retains 12398 starting tracked files, 2853 older non-Audit
production proofs, all 239 Haskell files, and all 206 active-package files.
All 74 frozen production manifests retain their 621 entries. Stashes and
three other worktrees retain their initial state.

No Haskell source change or new Haskell defect occurs. Root FINDINGS keeps
the external repair registry first. Field-pool repair b9219b9e is merged in
c0cc8a05. The Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`.
Derivation rejects the recursive pool; standalone holds retains opaque-pool
evaluation. Reuse the unchanged strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild evidence. Record each later Haskell repair with its
failure, reproducer, affected paths, commit, checks, and upstream status.

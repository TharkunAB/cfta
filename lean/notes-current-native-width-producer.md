# Current library proof status and initial native width production

This checkpoint starts at published 64d8b43d. Proof commits are 12846952
and ffb195b2. Source main remains c0cc8a05,
merged at 896b0a1c. The complete public Haskell theorem remains open.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target theorems. Support must describe initial inputs
and resources. It must not assume future success or the desired result.
Documented errors and validation order are observable results.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Exact transformations
require equality. Over-approximations require inclusion. Representative
selection has its own restriction contract. Distinct terms, accepting runs,
and generated members remain separate.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact size classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. | Host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired construction with nested Mu and unions. Initial syntax and captures bound allocations and complete stored and returned payload structure. | Haskell forcing, lazy publication, and runtime correspondence. |
| Checked recursive intersection | Initial numeric resources construct finite exact queries on established source domains. Joint current inventories retain captured origins for produced operands. | One initial resource producer for complete result-fed query sequences. |
| Original-source serial queries | One initial budget constructs finite lists of queries over a fixed original source with warm caches. | New operands outside that source and total memory capacity. |
| Generated optional binders | One initial source bound constructs result-fed optional binders and exact checked physical traces. | Other complete native query sequences. |
| Native code widths | Every node compiler branch and both checked edge branches derive quantitative code safety from initial physical inputs. No completed walk or future store is supplied. | Complete-query instruction count and physical word admission. |
| Actual native traces | Initial ready node and edge requests derive all reached width checks, causal stores, returned mass, and allocation bounds on the same actual checked trace. Warm and miss paths retain protected finish frames. | The actual physical trace and its length remain inputs. Construct them from initial resources. |
| Merge and selected Operand | Actual memo-aware Merge produces universal cap certificates. Selected domains construct finite Operands with unrelated open ordinary siblings. | Arbitrary constrained Mu bodies and runtime publication. |
| Mixed Edit and class pass | Actual reads and the tail-first class pass retain stores and finite syntax depth. | General first Target and Force misses and editor/class completion. |
| Ordinary constrained reduction | Initial profiles produce a resource Plan. A complete modeled pass retains guarded language and stores. | The domain excludes Mu, references, and unions in every descendant. |
| Other components | Existing language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted driver proofs remain preserved. | General descent, convergence, current adapters, and complete public pipelines. |

These are proofs for explicit modeled workers and caches. They do not prove
full correspondence with compiled Haskell execution. Theorem counts and
successful builds do not give a completion percentage.

## Quantitative code safety

SourceRecursiveIntersectionCodeMass.At records each literal Work input and
its square list limit. A continuation accepts any valid physical extension
with a larger causal store bound and an actual available or resident result.
It does not assume a returned mass or completed recursive execution.

The bind theorem retains the exact common state and bound. The walk theorem
retains both physical results and the exact original occurrence count.
Constructor helpers derive their own physical postconditions from verified
literal Work. Optional, node, and edge requests use actual physical returns.
Both native finish frames retain the certificate of their remaining code.

At is a quantitative and physical-result certificate. It does not prove
that a finish owns its running cell, that an enter is admissible, that a
request fits the machine word, or that execution completes. The actual
physical trace supplies those local input checks separately.

## Initial compiler producers

SourceRecursiveIntersectionCompileWidth covers the complete node dispatcher.
Original available values and Stored B bound union member counts and matched
row counts. Ordered continuations preserve these counts as the causal bound
increases. Actual Mu entry retains the original domain and body observations.
Actual binding reads use the current readback. The final compileNode theorem
requires only initial kernel validity, Stored B, and NodeReady.

SourceEqualityNativeCheckedWidth derives accepted child code from initial
resident rows. The original zip bounds the final constructor width. The
rejected branch derives its singleton-Empty width from store positivity.
Actual checked body yields retain their exact operation state and selected
code. Literal continuation binding uses the same physical native machine.
No completed walk, later-prefix store, or desired width law is supplied.

## Step preservation and complete prefix width production

SourceCurrentAllocatedNativeWidthStep.ControlAt includes code and demanded
edge-body continuations. Actual yielded instructions retain this certificate
at the common numeric MassTrace.ceiling. Native direct and warm returns,
miss publication, original captured requests, both protected finish frames,
reads, domain entry, literal Work, and optional binders are covered.
Actual Good, current physical inputs, fields, and the current causal store
derive every later physical and store fact used by a continuation.

SourceCurrentAllocatedNativeWidthTrace.widths follows any actual physical
Trace. Its initial ControlAt produces MassTrace.InputsThrough at every reached
instruction. Thus InputsThrough is now a derived result, rather than a public
future-width premise. prefix_bound derives the same numeric store and both
constructor-supply budgets. Domain allocation is at most the instruction count.

node_prefix and edge_prefix construct the initial request certificate from
Good and ready physical operands. They compute the initial store bound from
successful original heap records. No At, future store, or future width law
is supplied to these endpoints. node_return and edge_return also derive
actual execute, result mass, and supply bounds from a completed trace.

The public trace endpoints still take an actual physically checked Trace.
This includes its current key and finish-owner checks. Its fuel is the
actual trace length. The theorem does not yet construct a complete query or
derive its instruction count from initial data. It does not remove future
word admission from older completion theorems. These are the next producers.
Logical mass is not bytes. Conservative numeric ceilings do not establish
useful concrete headroom or total memory capacity.

## Remaining work

1. Derive a complete-query instruction count from the initial source and
   semantic recursion bound. Include ordered row/member expansion and native
   publication, demand, body, and finish costs. Warm tables may reduce work.
2. Derive raw-prefix physical input admission and word ranges from initial
   headroom. Combine the count with the proved width producer and numeric
   mass schedule. Construct the complete physical trace instead of supplying
   it. Retain actual finish ownership and current operation fields.
3. Compose complete queries that consume their actual preceding results.
   Retain populated native, equality, and global caches. Do not supply later
   entry counters or future WordRanges. Do not redefine public support to
   omit valid inputs.
4. Construct general Target and Force misses, mixed Edit, and ClassPass from
   initial resources. Produce active and stored outer-descent certificates.
   Cover arbitrary constrained Mu bodies. Keep the source gate that accepts
   closed no-Mu endpoints independently of their own guard.
5. Prove repeated reduction convergence. Complete remaining recursive pruning
   and compiler callers. One complete pass is not a fixed point.
6. Complete current typing/refinement adapters, drawn fields, symbolic
   measures, errors, validation order, and generator rank order. Complete
   solver, runtime, IO, randomness, concrete capacity, and user-code adapters.
7. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

Preserve all earlier proofs, counterexamples, repairs, and marked drafts.
Keep older constructor and equality work and the optimized interned core.
Do not repeat completed causal mass, initial code widths, native width-step
preservation, source-rebase, origin, Merge, selected-Operand, mixed-editor
cap, or serial optional-binder proofs.

## Validation and Haskell handoff

The pinned Lean 4.34.1 Audit passes 2876 jobs and 63991 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All five production
modules pass strict checks with empty final logs.
All 38 public declaration checks and ten constructive integration proofs pass.
All 48 full signature and axiom pairs pass in ten groups. Five component
manifests verify 142 entries. Complete imported signatures,
execution kernels, raw attempts, component manifests, and hashes are in
restart-evidence/20261017-native-width-producer. Read checkpoint-validation
and the component reviews for their exact checked scope.

Preservation retains 12796 starting files, 2870 older non-Audit production
proofs, all 239 Haskell files, all 206 active-package files, stashes, and
three other worktrees. All 76 frozen manifests retain their 633 entries.

No Haskell source changes or new defects occur. Root FINDINGS keeps the
external repair registry first. Field-pool repair b9219b9e is merged in
c0cc8a05. The Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds retains opaque-pool evaluation. Reuse unchanged strict Nix,
798 examples plus golden, Fourmolu, and Cabal-gild evidence. Record every
later Haskell repair with its failure, reproducer, paths, commit, checks,
and upstream status.

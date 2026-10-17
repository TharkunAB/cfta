# Current library proof status and native worker mass bounds

This checkpoint starts at published 3d1c966a. Its proof commits are de18ec41,
7f435218, and f8efa29a. Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

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
require language equality. Over-approximations require inclusion.
Representative selection has its own restriction contract. Distinct terms,
accepting runs, and generated members remain separate.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact size classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. | Host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired construction with nested Mu and unions. Initial syntax bounds allocation. Initial captures and stores bound full stored and returned payload structure. | Haskell forcing, lazy publication, and runtime correspondence. |
| Checked recursive intersection | Initial numeric bounds construct finite exact queries. Current inventories and captured origins retain joint laws for produced operands. | One initial resource producer for complete result-fed query sequences. |
| Original-source serial queries | One initial budget constructs finite lists of queries over a fixed original source with warm caches. | New operands outside that source and total memory capacity. |
| Generated optional binders | One computed initial source bound constructs result-fed optional binders and their exact checked physical trace. | Other complete native query sequences. |
| Native worker mass | Current validity bounds captured and returned native payloads. Actual checked edge, row, and union assemblers derive payload and identity bounds. Original operands derive emitter width checks. | Complete recursive production of all reached width and prefix-store certificates. |
| Numeric checked prefixes | A certified actual prefix derives causal store and constructor-supply bounds from initial source mass and step count. Every prefix bounds domain allocation by its step count. | The source compiler must produce the width certificate and complete-query instruction bound. |
| Merge and selected Operand | Actual memo-aware Merge produces universal cap certificates. Initial selected domains construct finite Operands with unrelated open ordinary siblings. | Arbitrary constrained Mu bodies and runtime publication. |
| Mixed Edit and class pass | Actual reads and the tail-first class pass retain stores and derive finite syntax depth. | General first Target and Force misses and editor/class completion. |
| Ordinary constrained reduction | Initial profiles produce a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Other components | Existing language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted driver proofs remain preserved. | General descent, convergence, current adapters, and complete public pipelines. |

The results concern explicit modeled workers and caches. They do not prove
full correspondence with compiled Haskell execution. A theorem count or a
successful build does not give a completion percentage.

## Actual constructor and native payload bounds

SourceRecursiveIntersectionWorkMass bounds literal makeNode, makeEdge, and
makeUnion execution. Full ordered list mass follows from element bounds and
literal list length. Union flattening and both final constructor paths use
at most one node request and no edge request. The store theorem retains
earlier warm winners. It does not bound arbitrary Work identify functions
or higher-order continuations.

WorkMass.Inputs combines actual physical constructor inputs with their
literal list limit. Its physical projection supplies the existing WorkInputs
check. run_bound derives the causal store and identity bounds from those
inputs. Pure Work changes no store; its arbitrary return value has no new
mass claim.

SourceCurrentAllocatedNativePhysicalMass derives the mass of each actual
captured request and returned cell from PhysicalCache.Valid and current
Stored. It covers both memo families and every cell phase. initial_cells
computes its own common source bound for arbitrary populated tables. Exact
successful current reads and resident child lists inherit the same bound.
An absent identity does not supply a payload. Individual payload bounds do
not bound the number of native cells or total table storage.

## Source worker assemblers and width producers

SourceEqualityNativeCheckedMass uses the actual ordered accepted child
WalkTrace. Physical Calls derive availability at its returned heap. Current
Stored bounds the accumulated children. The literal final edge constructor
produces its own result, fields, store bound, and zero-node/one-edge charge.
The rejected branch constructs its own singleton-Empty sentinel. Its bound
is max B 3. Actual body choice keeps the accepted and rejected branches
distinct. Exact checked Work yields retain populated native tables, domains,
and equality operations.

SourceRecursiveIntersectionCompileMass bounds actual hash-join occurrences
by the original row product and original node masses. It retains duplicate
occurrences. Union requests retain their original member count. Actual
completed row and union walks feed their own literal final constructors.
Both union orientations retain the selected compiler branch. The current
prefix Stored and residency inputs remain explicit preservation premises.

The two MassInputs modules convert original available or resident operand
bounds and actual completed walk lengths into WorkMass.Inputs(C*C).
The current numeric bound C must retain the original operand bound. These
local producers do not construct the earlier walk or its current store.

## Numeric checked prefix composition

SourceCurrentAllocatedRecursiveMassTrace uses:

`listLimit(B) = B * B`.

`ceiling(B) = max(inflate(listLimit(B), B), optionalCeiling(B))`.

`charge(B) = optionalCharge(B) + 1`.

Each actual step retains Stored(ceiling(B)) and both constructor-supply
bounds. This covers every stopping outcome. Physical checks give the
optional body availability. Literal Work inputs give the constructor width
and current availability or residency. Other instructions change no
constructor heap. Every instruction allocates at most one source domain.

massAfter and credit iterate these numbers without inspecting future
states. Their addition laws compose at the same numeric intermediate bound.
InputsThrough records only the additional reached Work width certificates.
An actual physical Trace, initial Good and Fields, initial Stored, and
InputsThrough derive the final store and both constructor budgets.
initial_prefix computes the initial Stored bound from the original heap.
Domain allocation needs no width certificate and is at most the step count.

InputsThrough is still an execution-prefix certificate. The complete source
compiler must produce it from initial inputs. The actual prefix length is
also not a derived complete-query instruction bound. These two missing
producers prevent a whole generated-query resource claim. Mass is not a
byte count. Conservative logical ceilings do not establish useful machine
headroom or total memory capacity.

## Remaining work

1. Produce a quantitative Code and protected-frame invariant from the literal
   node and edge compilers. Bound every captured list and continuation.
   Derive InputsThrough for a complete query. Retain earlier operands and
   all completed prefix results through the actual physical extensions.
2. Combine that producer with the initial finite scheduler. Derive the full
   instruction count, node and edge headroom, and domain headroom from the
   original input. Compose queries that consume their actual earlier results.
   Do not supply future WordRanges or later entry counters.
3. Construct general Target and Force misses, mixed Edit, and ClassPass from
   initial resources. Produce active and stored outer-descent certificates.
   Cover arbitrary constrained Mu bodies. Keep the source gate that accepts
   closed no-Mu endpoints independently of their own guard.
4. Prove repeated reduction convergence. Complete remaining recursive pruning
   and compiler callers. One complete pass is not a fixed point.
5. Complete current typing and refinement adapters. Include drawn fields,
   symbolic measures, errors, validation order, and generator rank order.
   Complete solver, runtime, IO, randomness, concrete capacity, and user-code
   adapters with explicit assumptions.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

Preserve all older proofs, counterexamples, repairs, and marked drafts.
Keep older constructor and equality work and the optimized interned core.
Do not repeat completed local mass, source-rebase, origin, Merge,
selected-Operand, mixed-editor cap, or serial optional-binder proofs.

## Validation and Haskell handoff

The pinned Lean 4.34.1 Audit passes 2871 jobs and 63915 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All seven new modules
pass strict checks with empty final logs. All 75 imported signature and
axiom pairs pass in ten groups. Five component manifests verify 161 entries.
Imported signatures, constructive kernels, raw attempts, and hashes are in
restart-evidence/20261017-native-mass-resources. Read checkpoint-validation
and the component reviews for the exact checked scope.

Preservation retains 12629 starting files, 2863 older non-Audit production
proofs, all 239 Haskell files, all 206 active-package files, stashes, and
three other worktrees. All 75 frozen manifests retain their 628 entries.

No Haskell source changes or new Haskell defects occur. Root FINDINGS keeps
the repair registry first. Field-pool repair b9219b9e is merged in c0cc8a05.
The Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds retains opaque-pool evaluation. Reuse unchanged strict Nix,
798 examples plus golden, Fourmolu, and Cabal-gild evidence. Record each later
Haskell repair with its failure, reproducer, paths, commit, checks, and
upstream status.

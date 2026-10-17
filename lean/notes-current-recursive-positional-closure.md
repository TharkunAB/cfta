# Current proof status and recursive positional closure

Checked on 2026-10-17 at proof commit `506d0843`.
The checkpoint starts at published `f83da569`.
Source main remains `c0cc8a05`, merged locally at `896b0a1c`.
The proof commits are `e3a2f22e`, `8b0a06eb`, and `506d0843`.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. The target is
a family of theorems. For each public operation P, its schematic form is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Support must describe initial inputs and explicit resource limits.
It must not assume successful completion or the desired future result.
The specification includes documented errors and validation order.
There is no complete whole-library implementation theorem.

The observable contracts include exact accepted terms at each node-count
size, counts, enumeration order, both rank/unrank inverses, transformation
language relations, generation coverage, and sampling probabilities.
Distinct terms, accepting runs, and generated members remain separate.
Exact transformations require language equality. Over-approximations require
inclusion. Representative selection has its own restriction contract.

## Established results and their limits

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact distinct accepted size classes, finite class evaluation, counts, retained row order, size-major enumeration, and both rank/unrank inverses. The finite carrier comes from validated graph keys. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled construction for repaired closed syntax, including binders and unions. Actual construction histories supply physical, semantic, and local hereditary facts. | Concrete lazy publication, interning, and runtime correspondence. |
| Recursive native intersection | A finite exact closed intersection from initial resource conditions. The same actual contextual receipt supplies scoped stores and local hereditary laws. Mu, references, and unions are included. | Machine capacity is explicit. General constrained outer progress and complete public callers are separate. |
| Finite ordinary constrained reduction | Initial profiles and constructor headroom derive the original raw-Reach resource Plan. The complete modeled pass preserves the full guarded language and retains stores. | The ordinary domain excludes Mu, references, and unions in every descendant. Total host runtime and memory are not bounded. |
| Recursive positional components | Finite projection from initial cap or path conditions. Required retains every supported original path at the same return. Plain edge calls complete in certified mixed memo tables. | Target intersections, edits, successive equality classes, mixed whole-node completion, and constrained recursive descent. |
| Other library components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver results. | Remaining current adapters and callers do not form a complete library theorem. |

The earlier native range gap is closed by
`SourceCurrentAllocatedRecursiveInitialRanges.initial_ranges` and
`cold_complete`. The caller does not supply future prefix checks.
The stronger same-return local laws are in
`SourceCurrentHereditaryNativeCold.cold_complete`.
The earlier status note records that range gap before its closure.
Read `notes-current-recursive-initial-ranges.md` and
`notes-current-hereditary-execution.md` for those results.

## New finite positional results

Thirteen additive modules extend the current component proofs.
`SourceCurrentConstrainedCap.Cap` permits a finite number of ordinary
constrained layers above hereditary recursive values. Its union case retains
the same bound on each alternative. Cap zero is hereditary annotation.
Actual constructors, head exposure, Required, and path projection retain the
bound and the causal Mu store. No global heap annotation is required.

`SourceCurrentConstrainedCapProjection.complete_endpoint` constructs its own
finite actual projection. A node path must consume at least the cap depth.
The forest theorem accounts for the first index selecting an original root.
That index does not consume an ordinary layer.

`SourceCurrentConstrainedCapPaths.Supported` describes the exact original
positions that lead to hereditary endpoints. It also supports safe paths
shorter than the uniform cap depth. PathExposure retains this condition
through the actual head. SupportedProjection constructs a finite projection
and proves annotation at that same result and returned heap.

`SourceCurrentConstrainedCapRequiredSupport.complete` constructs its own
Required graph from initial local facts. It retains the cap, causal Mu store,
and every original supported path. Ordered child relations retain signed
positions. Required needs a cap for every visited branch because it can
visit branches outside one selected path condition.

The conditional cache laws constrain only returned owners with empty own
equalities. The active-owner bound filters only plain owners. Other
constrained owners and their completed results remain permitted.
ConditionalPlainEdge constructs a finite actual edge call in those mixed
tables. HereditaryPlainEdge derives its plain-region condition from local
resident child annotations and closedness. The same execution retains strict
reads, the full caller Post, residency, shape, and the edge semantic law.
The initial conditional store and active-owner certificates remain explicit.

## Remaining work

1. Complete general recursive constrained reduction. Retain all outstanding
   path conditions through target intersections, actual edits, and successive
   equality classes. Different classes can overlap. Handle disjoint paths,
   equal paths, and both prefix directions. Derive support from actual result
   producers. Then prove a decreasing constrained recursive measure.
2. Extend the mixed-table edge result to whole plain nodes and their actual
   descendant walks. Produce the conditional store and filtered active bounds
   from each full caller's initial state and actual prefixes. A finite edge
   call does not prove a finite whole constrained pass.
3. Prove convergence of repeated reduction passes. Complete remaining recursive
   pruning and compilation callers. One exact pass does not establish a fixed
   point. Language narrowing alone does not bound intermediate structure.
4. Complete current frontend correspondence. Cover typing, refinement
   derivation, drawn fields, symbolic measures, errors, validation order, and
   generator-specific order.
5. Complete concrete runtime and external adapters. Cover maps and arrays,
   signed indexes and counters, lazy memo publication and forcing, global
   state, interning, codecs, solver answers, IO, and random draws. Keep
   primitive and user-code assumptions explicit.
6. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Discharge each
   remaining implementation adapter before claiming full correspondence.

## Haskell repair handoff

The reported recursive field-pool defect is fixed by `b9219b9e`, merged in
PR #65. The current source rejects a pool for a field of the datatype itself.
The retained Chain reproducer returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone `holds` still treats supplied pools as opaque. The repair rejects
the invalid derivation configuration. It does not change that evaluator.
Root FINDINGS keeps this repair and the external handoff first. It records
the failure, reproducer, affected paths, commit, validation, and merge status.
Historical failure reports retain their original bytes and source dates.
No Haskell change or new Haskell defect occurs in this checkpoint.

## Validation and preservation

The full pinned Audit passes 2747 jobs and 62089 dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.
All thirteen current sources pass strict checks without diagnostics.
All 144 imported axiom/full-signature pairs pass in 23 groups.
Nine component manifests retain 233 verified entries.
Integration kernels construct their own actual Required and projection calls,
including a short path that exposes Mu below an arbitrary constrained shell.
Other kernels construct serial edge calls through their exact returned states.
No completed enclosing query or future result law is a kernel premise.
The canonical build retains one older unused-variable warning.

Preservation retains 9862 starting files, 2733 older non-Audit proofs, and all
239 Haskell files. Sixty frozen production manifests retain 504 entries.
Stashes and three other worktrees remain unchanged.
The unchanged Haskell source retains its strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence.
These checks are component evidence. They do not give a meaningful percentage
of whole-library completion.

Read `restart-evidence/20261017-recursive-positional/` for strict logs,
imported probes, independent reviews, failed drafts, preservation checks,
and the next proof target. Preserve the optimized interned core and every
older proof, counterexample, repair, and marked draft. The full-library
goal remains active.

# Current library proof status and generated checked queries

Checked at proof commit 42d08285. This checkpoint starts at published f08ebe13.
The proof commits are ba847c76, 2a2ee885, and 42d08285.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target theorems. The complete implementation theorem
does not exist yet. Support must describe initial inputs and explicit
resources. It must not assume future successful execution or the desired
result. Documented errors and validation order are observable results.

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
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual source execution produces exact guard observations and causal body/probe equality. | Concrete lazy publication, interning, and runtime correspondence. |
| Checked recursive intersection | Initial numeric bounds construct finite execution with exact language, guard-depth caps, ranked occurrences, and exact memo laws. Concrete input inventories and captured request origins retain these laws when later queries consume produced operands. | Cumulative later-query budgets and full outer caller integration. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Mixed outer tables | Plain whole nodes and descendant walks construct finite execution in certified tables with other constrained owners. | General constrained node completion and initial production of active and stored certificates. |
| Rich editor and successive classes | Actual executions retain causal stores, original signed masks, caps, and physical/language receipts. Required execution constructs its finite return. | Current hereditary leaf support is smaller than the source gate. General class existence remains open. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

These proofs execute literal modeled source workers and caches. Complete
correspondence with the compiled Haskell runtime remains open. A theorem
count or successful check does not give a completion percentage.

## Source rebasing and captured origins

SourceWeightTransport proves exact weights only for identities with an
earlier successful payload read. An absent identity can acquire a payload
after allocation. An independent kernel proves that unrestricted source
weight equality is false. Free-name scope and coherent deep-name readback
restrict transported occurrence bounds to the earlier represented pairs.

CheckedJointOrigins retains original operands, source availability, original
bindings, and actual old reads for each enclosing pair. This invariant covers
every suspended, evaluating, and returned cell. Lookup records the new
request origin. Demand and finish preserve the original stored request.
They need no supplied result law to retain its origin.

CheckedJointRebase reconstructs the old antecedents of each conditional law.
Old original Mu witnesses and new annotated bindings identify the same
physical payload. New pure coverage and old residency recover the old input
conditions. Physical returned availability supplies coherent deep readback.
The theorem retains both joint memo families and their origins at the
current source heap. It changes no native cell or equality operation.
A vacuous conditional law alone is not used as evidence of old support.

CheckedJointOriginTrace uses the existing static admission certificate.
For a covered reference name, finite input reference closure supplies the
original Mu record. Other covered names use their original complete records.
The certificate derives each origin before lookup. Actual yielded steps
retain it through all memo phases. The full physical trace produces the
final origin store without a returned-result or future finish-law premise.

## Concrete models and finite generated queries

NativeInventoryCold computes the concrete two-root input inventory before
execution. Initial numeric counters derive all reached word checks. The
fixed-model query constructs its own receipt, contextual cache laws, and
all-cell admission. It does not reinterpret the arbitrary existential model
of the older cold endpoint.

NativeInventoryRebase computes the next inventory from the actual current
heap and `old.roots ++ [left,right]`. Immutable records and issued history
retain exact old ranks. The model admits both new closed resident operands.
Semantic contextual laws and all-cell admission remain at the same checked
state. This rebase requires no query execution or future range condition.

CheckedJointInventoryQuery.of_receipt interprets that receipt's own physical
trace. It derives the joint Context, returned cell laws, captured origins,
cap, occurrence classifier, Original, and ProbeFree. The inherited receipt
retains finite checked execution, exact intersection language, closedness,
physical effects, scoped caches, idle state, and the concrete input model.
Receipt.inventoryAt supplies the semantic inventory state for a later call.

CheckedJointInventoryCold constructs this full joint receipt from initial
Good, SemanticReady, GuardHeap, original available closed operands, their
caps, and numeric bounds. CheckedJointInventoryQuery.generated_complete
uses actual earlier stores and a concrete inventory. It rebases both semantic
and joint laws before it executes the next query. Newly produced closed
values can be its operands. Both native memo tables and the equality cache
remain populated. Neither endpoint assumes a supplied completed execution,
desired result law, or future WordRanges predicate.

For each entry heap node counter N and bits b, the bounds remain
`N < 2^b`, `edges.next <= 2^(b+2)`, and

`domains.next + 2^(N + N*N) < 2^(b+1)`.

The native width is b+2. Later calls require these bounds at their own actual
entry. This checkpoint does not derive all later bounds from one initial
budget. The conservative exponential domain bound is not a concrete
host-word capacity theorem. The cap family permits finite ordinary and union
prefixes over hereditary Mu bodies. Arbitrary constrained Mu bodies remain
outside this intermediate family.

Independent integration constructs a cold joint receipt and feeds its actual
result into the next query with an original operand. Every nonnumeric next
premise follows from that first receipt. The additional capacity condition
is causal at the first actual return. No prior completed receipt or final
machine is assumed by the cold caller. Other kernels check exact payload
growth, deep occurrence transport, warm hits, and repeated model expansion.

## Remaining work

1. Derive cumulative allocation bounds for serial calls. Retain exact issued
   identities and current native and equality caches. Do not replace an
   initial resource proof with a condition on future successful execution.
2. Produce universal finite-depth caps through actual memo-aware Merge.
   The existing hereditary certificate proves only annotated-input closure.
   Prove the new candidate law before publication. Recover any earlier
   keep-first winner from its captured original request.
3. Compose actual projection, Operand, Target/Fold, Force, Leaf, Edit, and
   the tail-first ClassPass. Use an explicit output depth transformer.
   At a mixed query, use a bound for both operands. Retain target slots
   indexed by the immutable captured class forest.
4. Prove general constrained recursive descent with the full source gate.
   The ordinary fast path accepts closed values without nested Mu before
   guard inspection. It does not imply hereditary annotation at every leaf.
   The existing rich hereditary family remains an intermediate domain.
5. Prove repeated reduction convergence. Complete recursive pruning and
   compilation callers. A complete pass does not establish a fixed point.
6. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete solver, runtime, IO, randomness, capacity, and
   user-code adapters with explicit assumptions.
7. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

The full library goal stays active. Do not repeat the checked intersection
trace induction, causal origin producer, or concrete-model source rebase.
Read caller-joint-rebase-review.md in the evidence directory for exact
current Haskell and Lean source locations for the remaining caller gap.

## Validation and Haskell handoff

The pinned Audit passes 2835 jobs and 63081 dependency checks. Only propext,
Classical.choice, and Quot.sound occur. All eight new production modules
pass strict checks without diagnostics. All 67 imported pairs pass in ten
groups. Five component manifests verify 123 entries. Read checkpoint-validation.json
in restart-evidence/20261017-joint-source-rebase/ for imported signatures,
integration kernels, component manifests, exact hashes, and raw attempts.
Canonical replay retains only the older unused-input warning.

Preservation retains 11815 starting files, 2826 older non-Audit production
proofs, all 239 Haskell files, and 70 frozen production manifests with 592
entries. Stashes and three other worktrees remain unchanged. Preserve all
earlier proofs, counterexamples, repairs, marked drafts, older constructor
and equality work, and the optimized interned core.

No Haskell change or new Haskell defect occurs. Root FINDINGS keeps the
external repair registry first. Recursive field-pool repair b9219b9e is
merged in c0cc8a05 and locally validated. The Chain example returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque-pool
evaluation. Reuse the unchanged strict Nix all-component build, 798 examples
plus golden, Fourmolu, and Cabal-gild evidence for this source.

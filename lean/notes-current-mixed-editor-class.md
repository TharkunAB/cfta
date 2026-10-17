# Current library proof status, mixed edits, and serial source resources

Checked at proof commit 140f5c7a. This checkpoint starts at published bf306940.
The proof commits are c0876d1a, 181f668f, and 140f5c7a.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input, resources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

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
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual source execution produces guard observations and causal body/probe equality. | Concrete lazy publication, interning, and runtime correspondence. |
| Checked recursive intersection | Initial numeric bounds construct finite exact queries. Concrete inventories and captured origins retain joint laws when later queries consume produced operands. | Initial resources for entire sequences that consume new results. |
| Original-source serial queries | One initial numeric source budget constructs any finite list of queries over that original source. Domain credit is shared across the whole list. Warm caches and exact language receipts remain present. | New operands outside that original source and concrete total memory capacity. |
| Memo-aware Merge and selected Operand | Actual Merge derives universal cap certificates before publication. Initial selected domains construct finite Operands with unrelated open ordinary siblings. | Arbitrary constrained Mu bodies and Haskell runtime publication. |
| Mixed Edit and class pass | Actual leaf, node, child, row, and list reads derive finite syntax depth bounds. Each class captures its actual entry forest. The tail-first pass retains full receipts, current native laws, and universal Merge laws. | General first target misses and editor/class completion from initial resources. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Other components | Existing language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted driver proofs remain preserved. | General constrained descent, convergence, current adapters, and complete public pipelines. |

These proofs execute literal modeled source workers and caches. Complete
correspondence with the compiled Haskell runtime remains open. A theorem
count or successful check does not give a completion percentage.

## Mixed stores and actual editor reads

MixedEditStoreEffects retains MixedShared.Stored through actual node and
raw edge construction. This store contains current-heap joint native laws,
captured request origins, universal Merge certificates, and target slots.
The exact constructor effects retain physical readiness and availability.

The actual recursive Head derives its returned guard heap. The initial
causal guard heap supplies the local Mu store. The same Head then produces
its result cap at the original finite depth. CurrentNative.advance retains
the actual native cells and equality operations. No returned guard law or
older hereditary native store is a premise.

MixedEdit follows every NodeReads, ChildrenReads, RowsReads, and ListReads
constructor. A leaf obtains its target and query cap from the same actual
MixedShared receipt. Ordinary rows retain their original raw guard and
ordered child arity. Selected children retain the actual earlier return
state before the next child. Recursive exposure retains the current stores
and derives the selected domain for the exposed input.

The output depth is a conservative proof-level syntax bound:

`outputDepth captured input edits = input + captured + sizeOf edits`.

The bound uses only the initial finite edit syntax and input depths.
It is a noncomputable logical size expression. It is not an executable
allocation estimate or a concrete runtime capacity bound. The child-list
bound reserves the map size. Row and node reconstruction account for the
parent layer. Unequal class path lengths do not require an identity depth
transformer.

The source selected-path gate remains explicit. Whole captured forests and
unselected ordinary siblings can stay open. A selected leaf is closed where
the source gate requires it. The proof takes no hereditary AtLeaves,
all-path Preserves, desired callback result, or future guard heap premise.
The earlier stronger mask theorems remain preserved as separate results.

## Actual classes and the tail-first pass

MixedClass.verified retains the same full ClassEdits.Receipt. A class clears
only its local target slots. Its captured forest is the literal input at
that class entry. Both native tables, equality operations, and the Merge
memo remain warm. Its output bound is:

`classDepth record d = outputDepth d d (compiled record)`.

MixedClassPass follows the actual right fold. Its bound first transforms the
tail depth, then applies classDepth for the head. The actual tail receipt
transports each head's selected domains to the returned forest. No assumed
intermediate cap or hereditary mask replaces that derivation. Final source
empty propagation retains every cap and changes no checked state or memo.

These production endpoints verify supplied actual reads. Integration can
construct its own pass under the older explicit operational Ranges plan.
That plan still constrains later reached states. It does not establish
general completion from one initial numeric budget.

## One initial resource budget for original-source queries

StaticQueries fixes an original physical source and its finite domain-key
inventory. Resources describes only that source, the initial domain cache,
and initial node, edge, and domain bounds. Current retains the actual past
domain allocation trace, immutable source records, and issued identities.

A later request uses operands already available in that same original
source. Their original scope survives actual heap growth. The existing
prefix certificate derives every reached word check from the original
resources and current past history. It does not require a bound on the
larger heap counters at that later entry.

The same actual query extends Current. Its full semantic receipt derives
the next concrete semantic input inventory at the actual current heap.
That semantic inventory can change. The domain-key resource inventory stays
fixed. These two inventories have different roles.

StaticQueries.complete constructs its own finite query, current native
laws, and result cap. complete_many constructs a finite serial Queries run
for any finite list of original operand pairs. Each next request starts at
the exact preceding returned state. It retains physical extensions, full
query receipts, semantic admission, global tables, result availability,
closedness, and caps. No later-entry counters or future WordRanges appear
in these completion premises.

The total domain supply satisfies:

`final.domains.next <= initial.domains.next + originalInventory.length`.

The complete actual allocation history also retains the missing-key credit
potential. Repeated calls do not pay the inventory bound again. This is a
shared serial resource result for original-source queries. It does not admit
new result operands outside that source. It does not bound total Haskell
heap memory, solver allocations, or host-word capacity for all public code.

## Remaining work

1. Construct general Target, Force misses, mixed Edit, and ClassPass from
   initial resources. The new class depth and store proofs discharge
   preservation obligations. General finite execution remains separate.
2. Extend the shared initial resource budget to queries that consume newly
   produced operands. Derive node, edge, and domain bounds across projection,
   Merge, recursive native queries, and reconstructed editor values.
3. Produce the active and stored certificates required by general constrained
   outer descent. Keep the ordinary gate that accepts closed no-Mu endpoints
   independently of their own guard. The finite cap family still retains
   hereditary Mu bodies. Arbitrary constrained Mu bodies need broader work.
4. Prove repeated reduction convergence. Complete remaining recursive
   pruning and compilation callers. A complete pass is not a fixed point.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete solver, runtime, IO, randomness, concrete capacity,
   and user-code adapters with explicit assumptions.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

The full library goal stays active. Preserve older constructor and equality
work and the optimized interned core. Do not repeat solved source rebase,
origin, Merge, selected Operand, or mixed editor cap proofs. Read
next-generated-resources-and-class-completion.md in the evidence directory.

## Validation and Haskell handoff

The pinned Lean 4.34.1 Audit passes 2849 jobs and 63208 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All five new production
modules pass strict checks with zero-byte logs. All 28 imported pairs pass
in eight groups. Four component manifests verify 98 entries. Signatures,
integration kernels, component hashes, and raw attempts are registered in
restart-evidence/20261017-mixed-editor-class/. Canonical replay retains only
the older unused-input warning.

Preservation retains 12120 starting tracked files, 2843 older non-Audit
production proofs, all 239 Haskell files, and all 206 active-package files.
All 72 frozen production manifests verify their 606 entries. Stashes and
three other worktrees retain their initial state. Preserve all earlier
proofs, counterexamples, repairs, and marked drafts.

No Haskell change or new Haskell defect occurs. Root FINDINGS keeps the
external repair registry first. Recursive field-pool repair b9219b9e is
merged in c0cc8a05 and locally validated. The Chain example returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque-pool
evaluation. Reuse the unchanged strict Nix all-component build, 798 examples
plus golden, Fourmolu, and Cabal-gild evidence for this source.

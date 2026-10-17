# Current library proof status and mixed caller depth bounds

Checked at proof commit 0a10b057. This checkpoint starts at published 5b0c56a8.
The proof commits are 0f90ca80, 8dfef438, and 0a10b057.
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
| Checked recursive intersection | Initial numeric bounds construct finite exact queries. Concrete inventories and captured origins retain joint laws when later queries consume produced operands. | Cumulative serial budgets and full outer caller integration. |
| Memo-aware Merge | The actual mutual graph derives universal finite-depth certificates before publication. Exact earlier winners retain their captured-original certificates. Comparison and selection retain guard heaps and joint native stores. | Completed-graph proofs do not prove Haskell lazy publication or runtime forcing. |
| Selected Operand | Initial selected-path domains construct finite projection and Merge with an explicit output depth. Unrelated ordinary siblings and captured roots can stay open. | Recursive heads still require the selected domain's closedness condition. |
| Target, Force, and Leaf | Supplied actual reads retain explicit depth bounds and populated stores. Slot misses establish universal certificates before storage. A warm-slot integration constructs its own finite Leaf from entry counters. | General target misses and full Edit/ClassPass completion from initial resources. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Other components | Existing language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted driver proofs remain preserved. | General constrained descent, convergence, current adapters, and complete public pipelines. |

These proofs execute literal modeled source workers and caches. Complete
correspondence with the compiled Haskell runtime remains open. A theorem
count or successful check does not give a completion percentage.

## Actual Merge and current native stores

MemoMergeCode.Certificate states:

`forall depth, Cap valid depth original -> Cap valid depth result`.

The literal branch proof covers small groups, the greater-than-four large
group threshold, retained columns, recursive boundaries, union construction,
selection, and identity returns. It derives the universal certificate from
the actual body graph and physical readiness. It does not take a result law
or an input cap as a premise. A caller supplies its input cap when it uses
the conditional certificate.

MemoMerge proves the actual mutual Run and Call graph. The smaller actual
run establishes the candidate certificate before remember. A keep-first
winner reads the exact earlier entry and its complete original input.
Both physical and universal memo stores follow the actual return state.
Constructive integration builds a positive-depth nonplain ordinary input,
constructs its finite cold Merge, and proves an exact same-state warm hit.

MergeGuardEffects retains semantic readiness, costs, and the guard heap
through actual row exposure, unfolding, comparison, and selection.
MergeJointEffects uses those effects through actual Merge calls. It retains
the semantic inventory and CurrentNative.At at the actual returned state.

CurrentNative.At combines the joint Context, both joint native tables, and
captured request origins at the current physical heap. Its checked step
interprets the same supplied physical trace. That trace derives the result
cap, closedness, Original, ProbeFree, and the next current-heap invariant.
This endpoint verifies an actual step. Earlier initial-resource endpoints
construct finite checked steps. Neither fact alone completes all callers.

## Selected projection and literal caller order

SelectedProjection uses NodeClosed, RowsClosed, and ForestClosed for the
selected path. It does not replace these conditions with closedness of every
captured root. An ordinary selector can ignore an unrelated open sibling.
A recursive head uses the domain's recursive closedness condition.
ProjectionGuard retains the actual guard heap without a closure premise.

MixedTarget.operand_complete constructs its own finite Operand graph and
receipt from initial readiness, selected domains, semantic coverage, stores,
and input caps. It assumes no supplied completed Operand or future ranges.
For a forest cap depth d and a signed path p, its output depth is:

`operandDepth d p = d - (p.length - 1)`.

Subtraction is natural subtraction. The first index selects a forest root.
Each later index consumes one cap layer. Independent kernels construct
finite endpoints with a nonplain ordinary selected value and open siblings.
Their initial physical readiness remains explicit.

MixedTarget.fold follows the literal order: head Operand, recursive tail,
then the checked query at that returned state. The query widens both input
caps to their maximum. The seed is the actual first path. An empty target
has depth zero. These endpoints verify supplied Target reads.

MixedShared.Certificate quantifies all captured forest depths and selected
operand domains. Each present slot retains that certificate for the immutable
class record, forest, and path. A Force miss derives it from the same actual
Target reads before storage. A hit reads the exact existing certificate.
Logical verification at a second depth does not execute the target again.

Leaf follows the actual Force before its query. Its depth is the maximum
of the captured target depth and the current input depth. The same actual
return retains current native laws, Merge certificates, and every slot.
No older all-path Preserves or hereditary AtLeaves premise is substituted.

Integration constructs an exact warm Force hit after a supplied actual miss.
A second kernel starts from legitimate initial warm-slot readiness and
numeric entry counters. It derives the query ranges internally, constructs
its own full Leaf receipt, and proves the maximum cap. Its slot table and
Merge memo remain exactly the initial ones. This kernel does not construct
the earlier slot history or arbitrary first misses.

## Remaining work

1. Lift the explicit depth transformer through actual Edit and tail-first
   ClassPass. Produce the required stored and active certificates. Retain
   slots indexed by the immutable captured class forest.
2. Construct general Target, Force miss, editor, and class completion from
   initial resources. The present Target/Force/Leaf production theorems
   verify supplied reads. Operand and the warm-slot Leaf kernel construct
   their own finite returns within their stated domains.
3. Derive cumulative physical and domain allocation bounds from one initial
   budget for serial calls. Current checked completion still needs node,
   edge, and domain room at each actual query entry. Warm-slot integration
   supplies only that particular leaf's initial query bounds.
4. Prove general constrained recursive descent with the full source gate.
   The ordinary fast path accepts closed no-Mu endpoints before guard
   inspection. Its own guard need not be plain. The cap family permits
   finite ordinary and union prefixes over hereditary Mu bodies. Arbitrary
   constrained Mu bodies remain outside that intermediate family.
5. Prove repeated reduction convergence. Complete remaining recursive
   pruning and compilation callers. A complete pass is not a fixed point.
6. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete solver, runtime, IO, randomness, concrete capacity,
   and user-code adapters with explicit assumptions.
7. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

The full library goal stays active. Do not repeat solved checked trace,
source rebase, origin, universal Merge, or selected Operand proofs.
Read next-editor-class-and-serial-resources.md in the evidence directory.

## Validation and Haskell handoff

The pinned Lean 4.34.1 Audit passes 2844 jobs and 63176 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All nine new production
modules pass strict checks with zero-byte logs. All 80 imported axiom and
full-signature pairs pass in 13 groups. Six component manifests verify 151
entries. Component hashes and raw attempts
are in restart-evidence/20261017-mixed-merge-caps/. Canonical replay retains
only the older unused-input warning.

Preservation retains 11952 starting tracked files, 2834 older non-Audit
production proofs, all 239 Haskell files, and all 206 active-package files.
All 71 frozen production manifests verify their 601 entries. Stashes and
three other worktrees retain their initial state. Preserve all earlier
proofs, counterexamples, repairs, marked drafts, older constructor and
equality work, and the optimized interned core.

No Haskell change or new Haskell defect occurs. Root FINDINGS keeps the
external repair registry first. Recursive field-pool repair b9219b9e is
merged in c0cc8a05 and locally validated. The Chain example returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque-pool
evaluation. Reuse the unchanged strict Nix all-component build, 798 examples
plus golden, Fourmolu, and Cabal-gild evidence for this source.

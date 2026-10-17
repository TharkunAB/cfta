# Current library proof status and causal guard production

Checked at proof commit b72ecdc9. This checkpoint starts at published 5ce2c90f.
The proof commits are 69f576ae, df35e4cd, and b72ecdc9.
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
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual source execution now produces exact guard observations and causal body/probe equality. | Concrete lazy publication, interning, and runtime correspondence. |
| Recursive native intersection | Finite exact closed cold intersection from initial resources. Ranked local constructors retain cap and occurrence laws. Positive ranked optional binders now construct finite returns with earlier-winner guard readback. | Joint mixed native induction and finite general warm callers. Initial probe-freshness and ranked support must be produced by those callers. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Mixed outer tables | Plain whole nodes and descendant walks construct finite execution in certified tables with other constrained owners. | General constrained node completion and initial production of active and stored certificates. |
| Rich editor and successive classes | Actual executions retain causal stores, original signed masks, caps, and physical/language receipts. Required execution constructs its finite return. | Current closed captured hereditary-leaf support is smaller than the source gate. General class existence remains open. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

Some theorems construct finite execution. Others verify supplied actual
reads or local continuation laws. These results have different premises.
Their theorem counts do not give a meaningful completion percentage.

## New actual guard producer

GuardSemantics interprets the full source syntax with structural and guard
observations. GuardNormalization proves exact profile equations through
literal edge construction, empty-child erasure, node and union normalization,
and root-reference filtering. These equations inspect stored payloads.
Language equivalence alone cannot supply them.

SourceHistory retains the actual earlier pre-probe semantic context and
depth heap. GuardHeap records equality of each actual stored Mu body's
profile and its exact ordinary probe's profile. GuardReadback combines
that equality with the actual depth-based cleanup decision. It derives the
returned profile from the current exact probes of an earlier stored winner.

GuardExecution proves this guard heap through the full actual source syntax.
Each smaller actual callback produces its observation before publication.
A fresh candidate establishes body/probe equality before keep-first writes.
An earlier winner retains its original certificate. Ordered child positions
retain paired structural and guard observations. The heap remains valid at
pending stopping states. Successful results have the exact interpreted
profile. Neither theorem takes a future successful callback or future guard
heap as an input. Closed construction derives the initial empty guard heap.

GuardNative applies the same executor theorem to actual stored substitution,
normalized native callbacks, and optional binders. It derives MuStored from
the guard heap. Complete initial caches construct finite optional-binder
execution and retain the causal heap, availability, and actual histories.
This completion result alone does not assert a finite returned cap.

GuardBinder adds the returned cap and ranked classification. Its initial
inputs include Ready, an available capped body, a produced guard heap,
a positive ranked classifier, the old pair's exact weight, and absence of
Depth and uninterned probe names from the body's free set. Intersection-only
free support derives those two freshness conditions. The proof constructs
both actual probes. It separately constructs the whole optional-binder
return. Literal execution equations align those same probes with the actual
canonical request. The actual selected final record supplies both returned
laws. This includes an earlier first writer. It does not assume a capped
candidate is the selected winner. The final cache retains full Ready.

These freshness and ranked conditions are substantive initial conditions.
Cap and Ready alone do not imply them. The complete native producer must
derive them at the appropriate call sites. This theorem does not establish
the full native source gate or arbitrary recursive request completion.

Independent kernel checks construct arbitrary closed syntax and then a
second source expression with the first actual value and cache. Another
kernel constructs an earlier raw Mu with nested binders and erased rows.
Its positive-cap smart warm return uses the produced invariant and leaves
the entire cache unchanged. The raw wrapper itself has no finite profile.
The bounded executable audit completes 19 fixtures, 38 cold/warm runs, and
50 same-cell observations without a profile mismatch. Timed-out subsets
remain unchecked. These experiments do not replace the source induction.

## Remaining work

1. Complete the joint recursive native producer. Combine exact input support,
   finite-cap and ranked laws, GuardHeap, Ready, and memo ownership through
   the same actual node/row/child/union execution. Derive each smaller request
   and its finite return from initial data. The positive optional-binder
   component and local continuation certificates now have proofs.
2. Construct finite warm Target, Leaf, editor, and class execution from each
   full caller's initial supported inputs and resources. Supplied traces
   and local continuation laws do not prove this existence result.
3. Prove general constrained recursive descent. Produce active-owner bounds
   and causal stores from initial callers and actual past prefixes. Retain
   the full source gate, which permits nonhereditary ordinary endpoints.
4. Prove repeated reduction convergence. Complete remaining recursive
   pruning and compilation callers. One pass does not prove a fixed point
   or bound intermediate structure.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete runtime, solver, IO, and randomness adapters. Keep
   capacity, primitive, and user-code assumptions explicit.
6. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Include serial
   warm calls and discharge each remaining adapter.

The current cap and captured closedness restrictions define an intermediate
supported family. The final theorem must cover the full source contract.
The complete library goal stays active.

## Validation and Haskell handoff

The pinned full Audit passes 2805 jobs and 62806 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All eight production
sources pass absolute-path strict checks without diagnostics. Imported
signatures, axiom checks, hashes, component manifests, and failed attempts
are recorded in restart-evidence/20261017-causal-guard-profile/.
All 134 imported pairs pass in 14 groups. Seven component manifests verify
181 entries. Read checkpoint-validation.json for exact hashes and groups.
Canonical replay retains one older unused-input warning.

Preservation retains 11200 starting files, 2796 older non-Audit proof sources,
all 239 Haskell files, and 67 frozen production manifests with 562 entries.
Stashes and three other worktrees remain unchanged. Preserve the optimized
interned core and every earlier proof, counterexample, repair, and marked draft.

No Haskell change or new Haskell defect occurs in this checkpoint.
PR #65 merges recursive field-pool repair b9219b9e in c0cc8a05.
Current derivation validation rejects the reported Chain pool with
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pool
evaluation. Root FINDINGS keeps the external repair handoff first, with
reproducers, affected files, commits, checks, and upstream status.
Reuse unchanged strict Nix all-component build, 798 examples plus golden,
Fourmolu, and Cabal-gild evidence for c0cc8a05.

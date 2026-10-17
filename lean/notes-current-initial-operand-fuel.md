# Current library proof status and initial selected Operand budgets

This increment starts at published 4ba9f2f4. Proof commits are 3d98c59e and
8a132c64. Source main remains c0cc8a05, merged locally at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target contracts. There is no completed universal public
library theorem. Specify the intended behavior first. Then prove that the
current Haskell implementation has that behavior. Support must use initial
input and resource conditions. It must not assume successful future calls or
the required result. Documented errors and validation order are observable.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws, transformation
language relations, generation coverage, and sampling laws. Language equality,
inclusion, and representative restriction have different contracts. Terms,
accepting runs, and generator members have different definitions.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. | Current host and solver adapters and full public composition. |
| Interned construction | Modeled repaired construction, including nested Mu and unions. Causal physical stores bound full returned and stored payload mass. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive row reads | Closed recursive collection and row exposure complete at initial computable fuel, with exact heaps, resources, literal output widths, and stable replay. | General caller composition and public runtime correspondence. |
| Comparison and selection | Repaired workers construct success from initial counters and causal mass. Exact histories, full heap bounds, ordered failed covers, and stable replay follow. | Complete caller composition and independent language-law hypotheses. |
| General memo-aware Merge | Initial resources compute sufficient work and selection fuel. Complete payload mass also supplies a scalar-only bound before a future argument exists. Exact returned heaps, memos, resource bounds, and larger-fuel replay follow. | General Target composition and Haskell runtime correspondence. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at an initial computable fuel ceiling. Full Mu, references, unions, swaps, resets, rows, and child traversal remain present. | General constrained callers and public runtime correspondence. |
| Native query programs | One initial forecast constructs finite indexed query programs that use actual preceding results. The same trace retains exact language, readiness, populated tables, captured origins, global validity, and resources. | Actual caller lowering, adaptive control flow, interleaved Target composition, and concrete capacity. |
| Selected Operand | Initial forest count, signed path, counters, and causal mass determine complete projection and Merge schedules. The endpoint constructs its actual Operand, exact worker observations, full allocated receipts, returned heap bounds, and complete query Frame. | General Target head/tail/query composition and concrete capacity. |
| Mixed editor and class pass | Actual reads and source class order retain stores and finite syntax depth. | General first Target and Force misses and complete editor and class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | General recursive values, outer descent, and repeated reduction convergence. |
| Other components | Earlier equality, arithmetic, union-find, memo, generation, ranking, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

A passing build or theorem count does not give a completion percentage.
These are explicit modeled workers and cache invariants. They do not yet
prove complete correspondence with compiled Haskell execution.

## Complete initial selected Operand producer

Seven additive modules close the complete selected Operand numeric boundary.

`SourceCurrentProjectionNumericReplay` uses static worker fuel
`2 * path.length + 1`. A recursive head returns an ordinary value, so one
path step uses at most one head instruction and one ordinary instruction.
Exact certificates retain every demanded read at one shared read fuel.
All certificate families support larger shared fuel. They keep the exact
rows, results, complete heaps, source order, and signed lookup branches.

`SourceCurrentProjectionUnionResources` derives a recursive read bound from
initial counters and causal mass. It separately derives the literal returned
row width from the same successful computed read. Residency alone cannot
bound duplicate occurrences. Ordered source union reads each operand at its
actual reached heap and then constructs the ordinary node. Its scalar
envelope retains original list multiplicity and every allocating unfold.
Head and union graphs derive their own shared replay certificates.

`SourceCurrentProjectionNumericControl` composes the ordered row bounds.
Each row step pays the current scalar and its shorter-path child bound.
The original row count stays separate from later scalar growth. An ordinary
projection pays that scan and its final source union. The complete path
envelope first pays a possible recursive head. All functions are pure and
computable. Their monotonicity retains exact ordered composition.

`SourceCurrentMemoMergeUniformNumeric` proves that complete value mass bounds
ordinary input height. An initial scalar q therefore supplies Merge fuel
`MergeNumericControl.bound q q`. A later caller can compute this fuel before
its projected argument exists. Warm results use actual causal stored mass.

`SourceCurrentProjectionInitialResources` derives every reached bound and
shared read certificate by path induction. Ordinary steps recurse only
through selected children. Recursive heads use the closed-head endpoint and
then the ordinary branch at the same path. `ForestClosed` remains unchanged.
Proper selected paths can retain unrelated open ordinary roots and siblings.
Negative and absent signed indexes keep their actual Empty branches.

`SourceCurrentProjectionNumeric.complete` constructs its own complete forest
graph from initial selected support. That graph executes at the computed
static work fuel and shared read fuel. The endpoint returns the same value
and full heap, semantic and cost facts, output availability and closedness,
final scalar resources, output mass, and exact larger-fuel replay.

`SourceCurrentConstrainedCapOperandNumeric.complete` constructs the actual
checked Operand, full existing receipt, and complete generated-query Frame.
Projection runs before Merge at its exact returned checked state. Initial
forest count, path, counters, and causal mass determine both schedules.
No future projected argument, intermediate heap, successful fuel, completed
call, or callback resource law is an input. Both exact worker equations and
both larger-fuel replay laws refer to the same actual receipt components.
The full native cells, loaded fields, inventory, global memos, and language
laws remain in those receipts and the returned Frame.

These are logical constructor-heap and worker-fuel bounds. They retain the
allocated equality-operation state but do not count its internal instructions
or establish a machine capacity bound. Merge replay observes the constructor
heap erasure of the same full allocated receipt. Haskell lazy publication,
concurrent forcing, solver work, bytes, and wall time remain separate.

## Immediate missing composition

Compose complete Target in actual head Operand, recursive tail, then checked
intersection order. Preserve the same captured forest and thread the exact
returned Merge memo, global memos, inventory, and Frame through every prefix.

The query resource Profile records node, edge, domain, and causal mass bounds.
The new Operand endpoint supplies node, edge, and mass bounds and preserves
the complete domain state. Convert it to the next Profile without reading
future counters. Compose query `Profile.step` only after the recursive tail.
Define the entire numeric schedule from initial paths and resources.

Derive the existing FoldRanges/TargetRanges or construct the raw fold with
equivalent initial numeric Room reservations. A later WordRanges condition
cannot remain a callback premise. Retain selected caps and Merge laws with
the existing mixed Operand receipt theorem. Query results must supply the
actual next cap and full Frame. A contiguous native-query sequence does not
alone prove this interleaved source order.

## Remaining library work

1. Complete general Target and Force with initial resource schedules.
2. Complete mixed Edit and ClassPass, initial active and stored outer descent,
   arbitrary constrained Mu bodies, and the complete source gate. Separate
   broader source support from stronger all-root cap assumptions.
3. Prove repeated reduction convergence and remaining recursive callers.
   One complete modeled pass does not establish convergence.
4. Complete current typing, refinement, and drawn-field source adapters,
   symbolic measures, errors, validation order, and generator rank order.
   Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
5. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines.

The complete library goal stays active.

## Haskell handoff

Root FINDINGS keeps the current repair registry before historical failures.
Repair b9219b9e is merged in unchanged source c0cc8a05. The Chain reproducer
returns `Left (FieldAtomOnDatatype "Next" 0)`. Derivation validation rejects
that configuration. Standalone `holds` still uses opaque pool descendants.
Reuse the existing strict Nix all-component checks, 798 examples plus golden,
Fourmolu, and Cabal-gild evidence. This increment adds no Haskell patch or
new behavior defect. Record each later fix in FINDINGS with its failure,
reproducer, affected paths, commit, checks, and upstream state.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2929 jobs and 64924 dependency checks.
All seven final production strict logs are empty. All 120 complete signature
and axiom pairs pass in ten groups: 100 public declarations and 20 constructed
checks. Only propext, Classical.choice, and Quot.sound occur. Four component
manifests verify 153 immutable entries. Read checkpoint-validation.json for
the exact sources, successful logs, and hashes.

Preservation retains 14099 starting files, 2921 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, two stashes, and three
other worktrees. All 85 frozen module manifests retain 686 entries.
Older proofs, counterexamples, repairs, and marked drafts retain their bytes.
Strict attempt sources and raw logs remain in the evidence directory.

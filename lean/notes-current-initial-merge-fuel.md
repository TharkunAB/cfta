# Current library proof status and initial general Merge budgets

This increment starts at published 5d0f928f. Proof commits are acc448b4,
c103620e, and efd8a685. Source main remains c0cc8a05, merged locally at
896b0a1c. The complete public Haskell theorem remains open.

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
| Recursive row reads | Closed recursive collection and row exposure complete at initial computable fuel, with exact heaps, resources, and stable replay. | Complete selected Operand numeric forecasts and public runtime correspondence. |
| Comparison and selection | Repaired workers construct success from initial counters and causal mass. Exact histories, full heap bounds, ordered failed covers, and stable replay follow. | Complete caller composition and independent language-law hypotheses. |
| General memo-aware Merge | Initial input height, counters, and causal mass compute sufficient work and selection fuel. The endpoint constructs the actual call, exact returned heap and memo, resource bounds, and larger-fuel replay. | Complete selected Operand composition, independent language laws, and Haskell runtime correspondence. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at an initial computable fuel ceiling. Full Mu, references, unions, swaps, resets, rows, and child traversal remain present. | General constrained callers and public runtime correspondence. |
| Native query programs | One initial numeric forecast constructs finite indexed query programs. Later calls use actual preceding results. Exact language, readiness, populated tables, captured origins, global validity, and numeric bounds follow on the same trace. | Actual caller lowering, complete interposed Operand numeric forecasts, adaptive control flow, and concrete capacity. |
| Selected Operand | Selected support constructs its actual projection and Merge and retains the complete generated-query frame. The mixed endpoint also derives its selected cap and retained Merge laws. | A numeric forecast for the complete Operand from initial forest and path data. |
| Mixed editor and class pass | Actual reads and the source class order retain stores and finite syntax depth. | General first Target and Force misses and complete editor and class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | General recursive values, outer descent, and repeated reduction convergence. |
| Other components | Earlier equality, arithmetic, union-find, memo, generation, ranking, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

A passing build or a theorem count does not give a completion percentage.
These are explicit modeled workers and cache invariants. They do not yet
prove complete correspondence with compiled Haskell execution.

## Initial general Merge producer

Six additive modules close the initial numeric Merge boundary from the
previous checkpoint. They retain the full source body and populated memos.

`SourceCurrentMemoMergeResourceCertificate.Checked` records each constructor
transfer at its actual reached heap. Bind checks the continuation at the
complete returned heap. Erasure retains the earlier physical certificate.

`SourceCurrentMemoMergeWorkWidths` derives literal constructor widths from
the original input mass. Ordered maps retain exact output lengths. Selection
cannot add occurrences. With original mass at most q, all actual direct Work
widths are at most `(q + 1)^2`. The proof retains both grouping branches,
retained-column normalization, and ordinary-union requests. It does not
require a finite ordinary profile. Actual memo winners can have larger mass
than new candidates; their bounds use the causal mass of the reached heap.

`SourceCurrentMemoMergeResourceTrace` attaches scalar bounds to the exact
measured graph. The code, returned value, complete heap, and complete memo
remain unchanged. A bounded trace derives one sufficient comparison fuel
for every actual selection. The trace is an intermediate proof object.
The complete endpoint derives it rather than taking it as an input.

`SourceCurrentMemoMergeNumericControl` defines pure computable functions.
Let W(q) be `(q + 1)^2` and C(q) be `100 * (q + 1)^3`. For smaller-height
call bound B(h), one step pays constructor growth, selection growth, the
child bound at the current scalar, and one instruction. B(0,q) is q + 2.
B(h+1,q) iterates that step C(q) times from q and adds one. The existing
controlled iterator is reused. Monotonicity supports exact ordered growth.

`SourceCurrentMemoMergeResourceIteration` follows the actual direct counted
graph. A request pays its exact measured child cost and one. Bind pays both
executed costs and one. It returns the same measured observation and a bound
for all reached heaps and the measured instruction cost. A local Requests
obligation names the exact direct request occurrences.

`SourceCurrentMemoMergeNumeric.call_bound` discharges Requests by induction
on ordinary input height. Initial physical facts derive smaller heights and
availability at the same actual request occurrences. The induction hypothesis
uses each request's reached scalar. Direct body counts pay all outer steps.
Warm hits retain their actual winner, complete heap, and complete memo.

`SourceCurrentMemoMergeNumeric.complete` accepts initial semantic readiness,
constructor-cost facts, physical memo storage, input availability, and causal
stored mass. Its work fuel depends only on input height, issued node and
edge counters, and that mass. Its selection fuel depends on that work bound.
It constructs its own successful Call and Worker return. It derives physical
effects, final memo storage, output availability, conditional closedness,
full resource bounds, output mass, and exact replay at both larger fuels.
No completed future call, final bound, selector receipt, or callback resource
law is a caller premise. Internal qualitative completion does not enter the
numeric formulas as a witness fuel.

The body domain remains the full source domain. Closed ordinary roots enter
grouping. Open ordinary roots, Mu, union, reference, and empty values return
directly. Independent language laws retain their cache and guard hypotheses.
This theorem concerns the completed sequential model. It does not establish
Haskell lazy publication, concurrent forcing, or concrete finite capacity.

## Immediate missing composition

Forecast the complete selected Operand from initial forest occurrence count,
signed path, counters, and causal mass. Compose actual projection first and
this general Merge second. Derive every reached resource bound from that
initial data. Return the same actual Operand and existing complete Frame.
Do not take a future projected heap, completed call, or desired bound as input.

Use `SourceCurrentAllocatedMergeOperand.Receipt` and its complete endpoint,
`SourceCurrentConstrainedCapOperandFrame`, the allocated projection resources,
and `SourceEqualityProjectionPathComplete`. Closed recursive reader and
selection bounds are already available. Preserve literal list multiplicity.
Availability alone does not bound duplicate occurrences. Preserve signed
index and missing-index behavior. A proper selected path permits unrelated
open ordinary roots; do not replace that domain by all-root closedness.

Then compose Target in actual head Operand, recursive tail, and checked query
order. Derive every reached query range from the initial schedule. Existing
finite ordinary Operand resource endpoints are restricted evidence and do
not replace the complete selected producer.

## Remaining library work

1. Construct the complete selected Operand forecast described above.
2. Complete Target and Force hits and misses with initial resource schedules.
3. Complete mixed Edit and ClassPass, initial active and stored outer descent,
   arbitrary constrained Mu bodies, and the complete source gate. Separate
   broader source support from stronger all-root cap assumptions.
4. Prove repeated reduction convergence and remaining recursive callers.
   One complete modeled pass does not establish convergence.
5. Complete current typing, refinement, and drawn-field source adapters,
   symbolic measures, errors, validation order, and generator rank order.
   Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines.

Work is atomic in the modeled interpreter. Its fuel does not count internal
constructor instructions, solver work, Haskell bytes, forcing, or wall time.
The complete library goal stays active.

## Haskell handoff

Root FINDINGS keeps the current repair registry before historical failures.
The recursive field-pool repair b9219b9e is merged in source c0cc8a05.
The unchanged Chain reproducer returns `Left (FieldAtomOnDatatype "Next" 0)`.
The source rejects that derivation configuration. Standalone `holds` still
uses opaque pool descendants. Existing strict Nix all-component checks,
798 examples plus golden, Fourmolu, and Cabal-gild evidence remain applicable
to the unchanged Haskell source. This increment adds no Haskell behavior patch.
Record every later Haskell fix in FINDINGS with its failure, reproducer,
paths, commit, validation, and upstream state.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2922 jobs and 64788 dependency checks.
All six production strict checks finish with empty logs. All 53 public
signature and axiom pairs pass. Thirteen constructed checks also pass.
All 66 pairs pass in eight groups. Only propext, Classical.choice, and
Quot.sound occur. Four component manifests verify 127 immutable entries.

The complete endpoint checks construct their own initial states. They cover
a five-row ordinary group, a five-row group with real Mu and union operands,
a productive Mu height-zero boundary, and two sequential computed calls.
The second call uses the exact heap and populated memo returned by the first.
It proves exact warm heap and table identity. Computed majorants stay symbolic.
The full recursive fixture does not separately prove an allocation-count
inequality. A separate ResourceTrace fixture proves allocating selection
between literal constructor jobs, followed by cold and warm Mu calls.
The WorkWidths warm fixture uses a physically admissible table; it does not
claim that an earlier body produced that table.

Preservation retains 13973 starting files, 2915 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, both stashes, and three
other worktrees. All 84 frozen module manifests retain their 679 entries.
Older production proofs, counterexamples, repairs, and marked drafts remain.
Failed proof sources and raw logs remain in the evidence directory.
Use current-strict-logs.json and kernel-logs.json for successful final inputs.

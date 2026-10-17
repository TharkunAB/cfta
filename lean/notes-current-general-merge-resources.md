# Current library proof status and general Merge accounting

This increment starts at published db0ec2b6. Proof commits are c28e7cb4,
b725b091, 17fcca53, and 9dba8b45. Source main remains c0cc8a05, merged
locally at 896b0a1c. The complete public Haskell theorem remains open.

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
| Recursive row reads | Closed recursive collection and row exposure complete with pure initial computable fuel, exact returned heaps, resources, and stable replay. | Full selected Operand numeric forecasts and public runtime correspondence. |
| Comparison and selection | Actual repaired workers construct success from initial counters and causal mass. Exact history, full heap bounds, ordered failed covers, and stable replay follow. | Global general Merge work and selection budgets and independent language-law composition. |
| General memo-aware Merge | Completed modeled calls, causal winner bounds, exact additive graph costs, static direct body cost, and local constructor/selection resource transfers. | One initial global work and selection budget across all recursive calls and interposed allocations. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at a computable initial fuel ceiling. Full Mu, references, unions, swaps, resets, rows, and child traversal remain present. | General constrained callers and public runtime correspondence. |
| Native query programs | One initial numeric forecast constructs finite indexed query programs. Later calls use actual preceding results. Exact language, readiness, populated tables, captured origins, global validity, and numeric bounds follow on the same trace. | Actual caller lowering, complete interposed Operand numeric forecasts, adaptive control flow, and concrete capacity. |
| Selected Operand | Selected support constructs its actual projection and Merge and retains the complete generated-query frame. The mixed endpoint also derives its selected cap and retained Merge laws. | A numeric forecast for the complete Operand from initial forest and path data. |
| Mixed editor and class pass | Actual reads and the source class order retain stores and finite syntax depth. | General first Target and Force misses and complete editor and class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | General recursive values, outer descent, and repeated reduction convergence. |
| Other components | Earlier equality, arithmetic, union-find, memo, generation, ranking, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

A passing build or a theorem count does not give a completion percentage.
These are explicit modeled workers and cache invariants. They do not yet
prove complete correspondence with compiled Haskell execution.

## General memo-aware Merge accounting

Four additive modules support the next initial Merge producer.
They do not yet construct a global initial resource budget for that producer.

`HeightOrderControlledMonotone` extends the existing controlled-vector
majorant. It proves monotonicity in the dimension and in the initial control.
Joint and diagonal bounds retain the original computable function.
The selection resource transfer uses these laws when causal mass increases.

`SourceCurrentMemoMergeResourceControl` uses one scalar bound for complete
stored payload mass and both issued counters. The initial counters and
causal mass establish that bound. Each actual edge, node, union, and ordinary
union job derives its next full-heap bound and actual returned payload bound.
Literal list width is a separate parameter. Returned old canonical winners
use their actual stored mass. The ordinary-union resource transfer permits
all input shapes; it does not impose a finite ordinary profile.

Selection derives its complete execution and exact larger-fuel replay from
current semantic facts, availability, closed inputs, and that current scalar.
Its resource envelope includes actual repaired unfold allocations. These are
local transfers at a proved current heap. They do not establish all current
heap bounds throughout recursive Merge.

`SourceCurrentMemoMergeMeasured` records exact additive costs for the actual
completed graph. Pure, work, selection, and warm hit each cost one. A request
adds its nested call cost and one. Bind adds both executed costs and one.
A miss adds its body cost and one. Erasure retains the exact code, result,
complete heap, and complete memo. Measured replay uses one shared selection
certificate at every demanded selection site. It proves exact worker replay
at all larger work and selection fuels. The supplied measured graph and
shared selection certificate are premises. This is a structural replay law.

`SourceCurrentMemoMergeDirectCost` counts direct body instructions while it
keeps nested request bodies opaque. Each direct request costs one and retains
its actual Call, argument, output, intermediate heap, and memo. Ordered maps
count their actual binds and returns. A source body with original full input
mass at most q has direct cost at most `100 * (q + 1)^3`. This cost bound needs
no final heap or semantic premise. Initial physical facts also derive strict
ordinary-height decrease for every direct recursive request on the same trace.
The direct bound excludes the costs inside those requests and selections.

The body domain remains the full source domain. Closed ordinary roots enter
grouping. Open ordinary roots, Mu, union, reference, and empty values return
directly. The accounting retains both group branches, retained-column
normalization, current first-winner rereads, and populated memo tables.
It does not substitute the finite ordinary profile worker.

## Immediate missing composition

Construct a pure work fuel, selection fuel, and resource envelope from the
initial literal input, ordinary height, node and edge counters, and causal
stored mass. Use initial semantic readiness, constructor-cost facts, physical
memo storage, and input availability. Derive the complete actual Call and
successful Worker.call at those fuels. Return the same value, full heap,
and full memo, with physical invariants and existing language contracts.

First classify every direct constructor job by its literal width and the
availability or residency of its actual inputs. Bound widths from the original
rows and columns and from exact returned map lengths. Compose local scalar
growth over the proved direct body count. Use strict request-height decrease
to pay nested calls. Derive one sufficient selection fuel at every reached
heap, including heaps changed by constructor jobs. Discharge the measured
replay certificate with those derived bounds. A future completed graph or
final resource bound cannot be an input of this initial producer.

The exact earlier memo winner can be larger than a new candidate. Use the
causal mass of the actual reached heap. A candidate-relative bound does not
control that winner. The global producer must preserve this case.

## Remaining library work

1. Complete the general initial Merge producer described above.
2. Forecast complete selected Operand work from initial counters, causal mass,
   forest occurrence count, and path length. Compose projection and Merge in
   source order. Preserve support for unrelated open ordinary roots.
3. Compose Target in head Operand, recursive tail, then checked query order.
   Derive reached ranges from initial inputs. Complete Force misses and hits.
4. Complete mixed Edit and ClassPass, initial active and stored outer descent,
   arbitrary constrained Mu bodies, and the complete source gate. Separate
   broader source support from stronger all-root cap assumptions.
5. Prove repeated reduction convergence and remaining recursive callers.
   One complete modeled pass does not establish convergence.
6. Complete current typing, refinement, and drawn-field source adapters,
   symbolic measures, errors, validation order, and generator rank order.
   Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
7. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines.

Work is atomic in the modeled interpreter. Its fuel does not count internal
constructor instructions, solver work, Haskell bytes, forcing, or wall time.
The initial numeric reader, comparison, and selection endpoints from the
preceding checkpoint remain proved. The complete library goal stays active.

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

The pinned Lean 4.34.1 Audit passes 2916 jobs and 64684 dependency checks.
All four production strict checks finish with empty logs. The complete
48 public signature and axiom pairs pass. This count includes 43 written
declarations and the five explicitly checked Counted constructors.
Ten constructed checks also pass. All 58 pairs pass in eight groups.
Only propext, Classical.choice, and Quot.sound occur.
Four component manifests verify 106 immutable entries.

The integrations include evaluated majorant dimensions, actual constructor
jobs before allocating selection, a published warm winner larger than Empty,
nested ordinary misses with exact larger-fuel replay, both source grouping
branches, and an actual retained ordinary-union request with warm replay.
Each check constructs its own initial heap or actual finite worker execution.
No future completion or resource result is supplied by the caller.
The measured integrations use finite concrete fixture execution; they do not
provide the missing general initial resource producer.

Preservation retains 13856 starting files, 2911 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, both stashes, and three
other worktrees. All 83 frozen module manifests retain their 673 entries.
Older production proofs, counterexamples, repairs, and marked drafts remain.
Failed proof sources and raw logs remain in the evidence directory.
Use current-strict-logs.json and kernel-logs.json for successful final inputs.

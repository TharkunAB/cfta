# Current library proof and initial parent and edge calls

Starting published checkpoint: 6adf1878. Proof commit: 5899990d.
Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Specify the intended behavior first. Then prove correspondence with the
current implementation. Support must depend on initial data and resources.
It must not assume a future successful call or its result. Documented errors
and validation order form part of the public contracts.

The contracts include exact term counts, distinct accepted terms per
node-count size, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts. Theorem totals do not establish a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes, counts, explicit row order, size-major enumeration, and both rank/unrank inverse laws. | Current adapters and complete public composition. |
| Interned construction | Modeled construction, nested Mu and unions, physical stores, and causal payload bounds. | Lazy forcing, publication, and Haskell correspondence. |
| Recursive reads | Initial resources construct closed collection and supported open WarmHead exposure with exact heaps and stable replay. | Arbitrary unsupported open recursion and remaining callers. |
| Comparison, selection, and Merge | Initial counters and causal mass construct modeled workers with histories, effects, memo state, and sufficient fuel. | Remaining callers, separate language hypotheses, and runtime correspondence. |
| Recursive intersection | Closed resident operands construct checked native queries, full Frame, origins, stores, language, and instruction bounds without finite input Caps. | Adaptive callers and public correspondence. |
| Operand, Target, Force, Leaf, and editors | Initial selected domains and reservations construct complete returns, language receipts, Frame, and Fits without finite input Caps. | Remaining recursive callers and runtime correspondence. |
| Complete allocated local reduction | Initial stored fields construct the precheck, reached Scan/Required/class continuation, strict reads, full old semantic receipt, and nine-fuel replay. | General outer recursive composition. |
| Parent edge and outer edge body | Initial live facts construct local reduction and actual edge reconstruction. Raw rejection skips fields and children. Full receipts, Frame, Fits, and Post use the same returned inventory. | Recursive node callers and runtime correspondence. |
| Outer edge memo call | Initial demand selects the actual stored owner. Ready, evaluated, and exact busy branches retain the complete caller. Successful completion excludes only the queried initial busy observation. | General node/row/descendant mutual recursion, progress, and convergence. |
| Ordinary recursive caller fragments | Initial finite ordinary profiles construct supported parent and mutual executions with guarded language and stores. | General constrained Mu inputs and supported open recursion. |

These Lean definitions are handwritten. They do not establish complete
correspondence with compiled Haskell. Earlier proofs retain their bytes.

## New initial parent and edge results

Five additive modules connect the complete initial local producer to the
actual allocated parent and outer edge result table.

MkEdgeNumeric.complete runs the actual checked edge constructor. It retains
the full existing receipt, same-inventory Frame, forecast Fits, exact node
counter, and at most one new edge. Its numeric profile uses the child count.
Constructor arity rejection retains the actual empty sentinel behavior.
MkEdgeNumeric.reject needs only the initial Frame and Fits. It needs no
stored field, inherited readiness, child availability, or query Room.

ParentForecast reads only initial raw fields and operations. A contradictory
raw edge reserves one sentinel constructor and no local work. A live edge
reserves its local producer and final constructor. The resident forecast
loads the original field from the initial operations. It does not quantify
over a future returned state or graph.

ParentNumeric.complete constructs the actual raw-rejected or live parent
worker. Its live facts are conditional on raw contradiction being false.
The live branch executes the complete local producer, then the constructor
at that actual returned checked state and inventory. The full old receipt
retains physical stores, memo histories, arity, and guarded language.
Strict reads, Frame, Fits, and caller Post refer to the same execution.
All nine lower worker fuels can increase independently.

ParentNumeric.resident_complete derives the initial cached load and child
availability from initial readiness and live residency. Its raw rejection
branch does not need residency or inherited readiness. This endpoint gives
its own resident forecast Fits and nine-fuel replay.

EdgeBodyNumeric.complete wraps that actual parent return. It derives the
inherited-conditioned EdgeLaw from the complete parent language receipt
and the original structural edge meaning. No future result law is supplied.
The graph retains the conditional source field load and strict reads.
The complete old edge receipt, Frame, Fits, and Post use the same inventory.
The actual edge body does not consume its outer recursion fuel. Replay
therefore permits any outer fuel, including zero.

EdgeCallNumeric inspects only the initial beginEdge demand. A ready hit
needs no parent reservation and retains the exact complete caller. An
evaluation runs the actual first published owner at the actual post-demand
state. The selected owner can differ from the candidate request. The proof
retains its physical key, protected evaluating cell, returned result, and
candidate language law. The finish publishes that exact returned result.
All nine lower fuels can increase independently. Outer fuel stays arbitrary.

The finite_or_busy endpoint retains the exact busy diagnostic and returned
caller for every fuel choice. Its successful alternative constructs a full
receipt. The complete endpoint excludes only the queried initial busy
observation. It does not require every table cell to be idle. Valid initial
tables and inherited readiness rule out the absent observation.

Initial Context, Frame, Fits, live cached fields, inherited readiness, child
availability, and pure reservations remain explicit. Resident endpoints
derive the live field and availability facts. No future graph, reached
range, successful worker, returned invariant, finite input Cap, or
whole-forest closedness is a producer premise. No finite output Cap is
claimed. Selected lower-level recursive queries keep their required domains.

Reservations are partly noncomputable logical majorants. They do not give
extracted Haskell budgets, concrete host capacity, or actual lazy memo events.
True memo answers establish emptiness. False answers do not establish
nonemptiness.

## Missing work

1. Compose the complete edge call with outer node calls, ordered rows,
   descendants, inherited prefix construction, and mutual recursion.
   Derive their reservations from initial source data. Preserve actual
   returned state and first-published owners.
2. Prove progress and convergence for the intended recursive domain.
   Cover general constrained Mu and supported open inputs. Retain the
   source policy for unsupported references and busy cells. Do not assume
   future termination or require all table cells to be idle.
3. Connect the handwritten workers to current Haskell adapters, lazy
   forcing, publication order, concrete memo events, documented errors,
   runtime, and resource capacity.
4. Compose every public language, counting, enumeration, ranking,
   generation, and sampling contract through those adapters. Keep
   exactness, inclusion, and representative restriction distinct.

## Evidence and Haskell handoff

Read restart-evidence/20261017-initial-parent/README.md and
checkpoint-validation.json for exact probe and manifest counts.
All five final strict logs contain zero bytes. All five canonical targets
pass. Audit passes 3025 jobs and 66039 theorem dependency checks under
4 GB MemoryMax, 4 GB MemoryHigh, zero swap, and 361 MiB peak memory.
Failed attempts retain their immutable source and raw logs.
Public signatures, proofs, selected Receipt projections, constructed
integrations, and axiom dependencies have separate checks.
Only propext, Classical.choice, and Quot.sound are permitted.

Preservation retains all 16349 starting tracked files, 3019 older non-Audit
sources, 239 Haskell files, 206 active-package files, both stashes, three
other worktrees, and 99 frozen module manifests with 782 entries.
Audit adds only the five new imports. Older proofs and evidence keep
their bytes. The optimized interned core remains included.

This checkpoint adds no Haskell change or new behavior defect. FINDINGS
keeps the external repair registry first. Field-pool repair b9219b9e is
merged and validated in unchanged source c0cc8a05. The Chain reproducer
returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains
opaque-pool evaluation. Record every later Haskell repair with its failure,
executable reproducer, affected files, commit, checks, and upstream status.
The whole-library goal remains active.

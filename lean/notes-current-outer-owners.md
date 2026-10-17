# Current outer owners and the remaining general progress proof

Starting published checkpoint: 4e4f0d60. Proof commit: ba6639ec.
Source main remains c0cc8a05,
merged at 896b0a1c. The complete public Haskell theorem remains open.

## Whole-library target

For every public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Specify intended behavior first. Then prove correspondence with current
Haskell. Support must depend on initial data and resources. It must not
assume a future successful worker, graph, or returned result. Errors and
validation order are part of the contract. Exact accepted terms, counts
by size, enumeration order, rank/unrank inverses, transformation relations,
generation, and sampling remain separate public obligations.
The earlier component map is in notes-current-outer-progress.md.

## New checked owner facts

| Module | Result | Boundary |
| --- | --- | --- |
| OuterKeyIdentity | Equal physical keys identify both complete arguments of ready available node requests and ready resident edge requests. An actual evaluation captures exactly the queried request. | Requires a valid equality interner, coherent records, Ready inherited values, and availability or residency. Evaluation also requires Sound. Stored alone is insufficient. |
| OuterBusyOwners | Every bounded literal mutual worker retains an evaluating captured request at the handle of any reported outer busy fault. Immediate busy demands retain the complete caller and its query-key entry. | Holds even for malformed tables. The owner is existential. It need not equal the query without the additional key-identity premises. This is no busy-exclusion or ancestry theorem. |
| OuterEdgeIdle | Every bounded literal phase, started without evaluating edge cells, preserves that condition on success and cannot report an outer edge-busy fault. Initial empty outer tables derive this condition. | Node owners may remain evaluating. A failed edge body can leave its selected edge owner evaluating, but the failure propagates before another demand. Other faults and incomplete runs remain possible. |
| OuterCopiedWarmHit | A source-built admitted root reaches the internally copied constrained child after its first evaluation returns. The copied request is ready while the root and wrapper owners remain evaluating. | A finite logical prefix, not general completion or host demand correspondence. Its phase relation has checked failure transport through the literal worker. |
| NativeGuardOccurrenceGrowth | An actual native memo execution on source-built closed operands increases constrained-level counts from 1 and 1 to 2. Full physical own fields are retained in the witness. | Refutes maximum preservation for this count. It does not refute the existing distance-based Cap profile, prove divergence, or identify a Haskell defect. |

Ready means Stored plus well-formed canonical inherited metadata. Equal
canonical identities alone do not reconstruct malformed Record.paths.
The key proof reuses the existing inherited-value identity and physical
record uniqueness laws. It does not assume a rank. Any rank defined only
from those complete literal request arguments is therefore key-compatible
under these premises. Extra historical occurrence labels need a separate
compatibility argument.

The edge result family completes before child recursion starts. Its body
runs the parent worker without outer recursive calls. If it succeeds, the
edge call finishes that owner before descendants. If it fails, every bind
returns the reached fault and caller immediately. The direct fuel proof
uses no supplied successful graph, semantic context, node-idle condition,
Cap, closure, or rank. Starting edge idle is enough. This removes outer
edge-busy faults from the general initial-run progress obligation.
It does not establish physical memory capacity or host evaluation order.

## The copied child at the actual internal demand

The fixture builds constrained finite B = pair(leaf,leaf), plain productive
tau = mu x.(leaf | pair(x,x)), and a root with class [0]=[1,0]. B retains
its own class [0]=[1]. Initial construction, allocation history, Ready,
availability, and closure are derived. Both outer tables start empty.

The first B demand has fuel 21. It returns B at cell 1. An exact literal
prefix from root fuel 24 then reaches the copied B demand at fuel 17.
At that pre-demand caller, the complete inherited values and complete
request keys agree. The copied payload is B itself. Cell 1 contains the
original request and returned B. Root cell 0 and wrapper cell 3 still
evaluate. The copied demand and node call return ready B and keep the
exact same full caller. This is an internal hit, not an inference from
the final state of the whole outer run.

Phase.run executes each literal worker phase and erases only successful
output values. Step.failed and Reached.failed prove that a failure at a
reached phase returns the identical fault and full caller from the initial
phase. Every transition uses an actual completed preceding prefix or a
literal branch. The selected fixture is finite. This is a prefix relation with failure transport. It is not a full event
trace or a simulation of successful continuations. This correspondence is
for the logical worker. Verified Haskell extraction and lazy demand order
remain open. The earlier whole fixture completion remains preserved.

## Remaining general progress obligation

The next certificate must order fresh node evaluations after actual local
parent returns. It must account for inherited combine/descent, native
products, unequal-length edits, and already returned memo winners.
Ordinary height is not a strictly decreasing measure. The actual earlier
parent witness increases edge height from 2 to 3. A maximum of constrained
ordinary levels also fails: a native product stacks the distinct levels
of its two operands. A finite guard alphabet supplies no ordering of the
actual original occurrences.

Ready hits need no fresh body descent. The internal fixture checks this
case while enclosing owners remain active. The remaining node-busy proof
must relate the actual nested query to each captured active owner. A
history-dependent rank must agree across same-key owner reuse, or the
proof must establish key-disjointness. Ghost-label descent alone does not
exclude a busy physical cell. Existing logical resource majorants are not
such a rank. No output Cap or future rank is made an input producer premise.

After that producer, finish nonempty live walks, ordered rows, ordinary
node bodies, and the full mutual pass. Repeated-pass convergence remains
a separate obligation. Current frontend/error adapters, lazy forcing,
memo publication, concrete memo events, host capacity, public pipeline
composition, and full Haskell correspondence remain open.

## Validation

All five final strict source logs are empty. All five final canonical
targets pass. Full Audit passes 3040 jobs and 67182 dependency checks
under 4 GiB MemoryMax, 4 GiB MemoryHigh, zero swap, and 608 MiB peak.
Only propext, Classical.choice, and Quot.sound are permitted. Read the
evidence README and checkpoint-validation.json for exact probe counts.
Failed and superseded attempts retain their source and raw output.

## Preservation and Haskell handoff

No Haskell source change or new Haskell behavior defect is added.
Field-pool repair b9219b9e is already merged and validated in unchanged
source c0cc8a05. The original Chain example returns
Left (FieldAtomOnDatatype "Next" 0). Standalone holds retains opaque-pool
evaluation. Reuse the existing unchanged-source validation.
FINDINGS keeps the external repair registry first. Every later repair
must record its failure, executable reproducer, affected paths, commit,
checks, and upstream status there.

All prior proofs, counterexamples, repairs, marked drafts, optimized
interned code, stashes, and other worktrees remain in scope for preservation.
Evidence is in restart-evidence/20261017-owner-progress/.
The whole-library goal remains active.

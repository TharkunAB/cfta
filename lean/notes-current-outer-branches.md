# Current library proof and initial outer branches

Proof commit: `85ba15b0`. Starting checkpoint: `48fdc955`.
Audited Haskell main remains `c0cc8a05`, merged at `896b0a1c`.
The whole-library goal remains active.

## Whole-library target

For each public operation, prove termination and its specified result from
valid initial inputs and initial resource conditions. Specify the intended
behavior first. Then prove correspondence with the current implementation.
Support must not assume a future successful worker, graph, or returned law.
Documented errors and validation order are part of the public contract.

The target includes accepted terms, exact counts by size, enumeration order,
rank/unrank inverses, language relations, generation, and sampling laws.
Terms differ from accepting runs. Exactness, inclusion, and representative
restriction differ. Theorem counts do not measure completion.

## Current proof map

| Component | Established modeled result | Remaining boundary |
| --- | --- | --- |
| Sized queries | Exact term classes, counts, row order, enumeration, and rank/unrank laws. | Current public adapters and complete composition. |
| Physical construction | Nested Mu, unions, stored winners, allocation bounds, and causal payload mass. | Concrete lazy evaluation, publication, and runtime correspondence. |
| Readers, comparison, selection, and Merge | Initial resources construct supported workers with exact heaps, effects, histories, memo returns, and sufficient fuel. | Unsupported open recursion and remaining callers. |
| Recursive native intersection | Closed resident operands construct checked Mu/reference/union queries with language, Frame, origins, stores, and instruction bounds. No finite input Cap is needed. | General outer recursive composition and Haskell correspondence. |
| Local reduction | Complete initial Scan, Required, class pass, Target, Force, Leaf, and editor producers retain strict reads, language, Frame, Fits, and caller Post. No finite input Cap is needed. | General outer recursive calls. |
| Parent and outer edge calls | Initial live facts and reservations construct the parent, edge body, and captured-owner edge call. Raw rejection skips fields and children. | General node, row, and descendant mutual recursion. |
| New outer branches | Initial inherited prefixes, raw reconstruction, terminal node bodies/calls, and terminal descendants retain their actual receipts and numeric resources. | Nonempty live child walks and ordinary recursive node bodies. |
| Earlier finite ordinary completion | Initial finite ordinary domain facts establish supported mutual completion. | Extending its shape and returned-height laws to the general source domain. |

These handwritten Lean proofs retain their selected-path, physical,
semantic, and initial reservation conditions. They permit unrelated open
forest roots. They do not prove full compiled Haskell correspondence.

## Exact support added at this checkpoint

[RawRebuildNumeric](MicroCFTA/SourceCurrentRawRebuildNumeric.lean) adds
same-inventory Frame and constructor Fits to the actual raw receipts.
`edge` needs a resident original edge, available replacement children, and
equal arity. It retains the original raw field and ordered children. Nodes
stay fixed; edges grow by at most one. Equality operations stay exact.
`modify` needs an available ordinary input and resident returned rows.
Equal ordered row identities retain the full checked state. Changed
identities run the actual node constructor. Nodes grow by at most one;
edges stay fixed. These local transfers do not complete the preceding
child or row worker.

[InheritedNumeric](MicroCFTA/SourceCurrentInheritedNumeric.lean) constructs
its own inherited-first prefix and indexed descent. Inherited contradiction
needs no field, residency, or inherited readiness premise. The live branch
uses initial field availability and inherited readiness. The resident
endpoint derives the field from actual edge residency. Prefix and descent
retain the same inventory, native profile, and global memo bundle. Equality
operations can grow. This module makes no recursive outer child call.

[NodeTerminalNumeric](MicroCFTA/SourceCurrentNodeTerminalNumeric.lean)
constructs Empty, explicit union, and Mu bodies. Empty and union return
immediately. Union alternatives can be open. Resident Mu rebuilding follows
from initial Context, available input, and filtered probe history. Cleanup
can remove the binder. The full caller remains unchanged. The complete
receipt retains strict reads, Checks, NodeLaw, Post, Frame, and Fits.
All ten literal worker fuels are arbitrary, including zero. An unresolved
reference is not a terminal case in this result.

[NodeCallNumeric](MicroCFTA/SourceCurrentNodeCallNumeric.lean) handles an
actual ready node cell for every input shape. The hit retains the full
caller and needs no body reservation. For terminal evaluation, demand
selects the actual stored owner and running caller. Physical identity
derives the owner's terminal shape. The producer runs that body and
finishes the same captured cell with its exact result. The receipt retains
the candidate language law, strict reads, Post, Frame, and Fits.
`finite_or_busy_terminal` preserves the exact busy fault or constructs its
own return. `terminal_complete` excludes only the queried initial busy
observation. Other cells can remain busy. All ten fuels remain arbitrary.

[DescendantsNumeric](MicroCFTA/SourceCurrentDescendantsNumeric.lean)
constructs its own prefix, terminal children, and raw rebuild. Its initial
condition is either a contradictory result of the initial prefix or an
empty original child list. Contradiction erases all original child slots.
A live empty list uses the actual empty walk. The result retains the raw
field, arity, resident output, guarded EdgeLaw, strict reads, same-inventory
Post and Frame, constructor Fits, and all ten fuel equations. It does not
complete a nonempty live child walk.

The profile bounds constructor node and edge supplies, native domains,
and stored constructor payload mass. It excludes equality-operation record
counts. Context and the receipts retain their actual validity and growth.

These initial producers assume no finite Cap, whole-forest closure, future
graph, future worker success, reached range, or desired result law. They
retain legitimate initial Context, Frame, Fits, availability, residency,
and equality readiness where their branch needs these facts. The new
terminal producers need no query Room. Earlier nonterminal local producers
retain their initial reservations. Some pure majorants are noncomputable;
they are not extracted Haskell budgets or concrete host capacity estimates.

## The exact height barrier and missing recursion proof

[OuterHeightBarrier](MicroCFTA/SourceCurrentOuterHeightBarrier.lean)
constructs the actual closed plain source `mu x. step(x)`. Its primary gate
returns `some false` on the original two occurrences and paths
`[[0,0],[1,0]]`. Its actual Head and Required graphs raise ordinary height
from **0 to 1**. The witness starts from source construction and derives
availability, closure, and semantic readiness itself.

This refutes general Required height nonincrease. It proves no full parent
height increase, outer cycle, divergence, or current Haskell defect. The old
finite ordinary proof remains valid: its domain excludes Mu and explicit
unions, and it carries a separate returned-height law. Those premises cannot
be removed by reusing ordinary height on the general recursive domain.
The live source [gate and Required implementation](../cfta/src/Data/CFTA/Equality/Operations.hs)
accepts a closed unconstrained Mu during the primary test and exposes its
head for a nonempty requirement. Its comments also leave general mixed
progress and repeated-pass convergence open.

The next missing result is initial completion of nonempty live child walks,
ordered rows, and ordinary node bodies through their full mutual recursion.
It needs a causal progress certificate for actual returned children and
captured warm owners. The proof must initialize that certificate, retain it
through actual parent work, install it before finish, and recover it at the
same owner's hit. A desired returned-child rank premise would leave this
producer open. Local resource growth bounds are not decreasing call ranks.
Unequal-length edits can move constrained values into deeper unfoldings.
Pending path work is a possible measure, not a proved solution. One-pass
completion and repeated-pass convergence remain separate obligations.

## Validation, runtime boundary, and source repair

The six final strict logs are empty, and their canonical targets pass.
Audit passes **3031 jobs and 66145 dependency checks** under **4 GiB
MemoryMax, 4 GiB MemoryHigh, zero swap, and 367 MiB peak memory**. It replays
only the old ClosedCompletion unused-input warning. Checks permit only
`propext`, `Classical.choice`, and `Quot.sound`. Failed sources and raw logs
remain immutable. The [checkpoint review](restart-evidence/20261017-initial-outer/resources-review.md)
links the scope to its constructed checks. The [Audit execution record](restart-evidence/20261017-initial-outer/audit-execution.json)
records the effective limits and successful exit.

No Haskell change or new Haskell behavior defect is added. Field-pool repair
`b9219b9e` is merged by PR #65 into unchanged source `c0cc8a05`.
The Chain reproducer now returns `Left (FieldAtomOnDatatype "Next" 0)`.
It rejects the invalid recursive field-pool configuration. Standalone
`holds` keeps opaque-pool evaluation. The [retained executable output](restart-evidence/20261016-drawn-fields-local-worker/source-derive-self-field.log)
and [current repair registry](../FINDINGS.md) separate the repaired source
from the historical failure.

Current frontend/error adapters, lazy forcing, publication order, concrete
memo events, host capacity, and full public Haskell correspondence remain
open. Green Lean components and earlier Haskell checks do not prove these
connections. The whole-library goal is not complete.

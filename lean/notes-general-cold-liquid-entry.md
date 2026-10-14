# Complete encoded Sized queries from general repaired cold construction

Updated: 2026-10-14 23:31 CEST.
Proofs: `4d1240dc` and `e7ab540a`. Source base: `origin/main` at `f201deda`.
Repository: `TharkunAB/cfta`. Publish checkpoints on `formalize`.

## Source composition

This proof composes `Data.CFTA.Interned.toFTA` with
`Data.CFTA.Sized.sizedUpTo`. `toFTA` checks the physical free variables,
reads the complete cold rows, and calls `mkFTA`. `mkFTA` merges duplicate
keys, sorts the map, and checks the initial state, children, and alphabet
arities in that order. Successful conversion supplies the actual explicit
graph for bounded encoded solver execution.

The previous restart target overstated what root membership and child
closure prove. They remove missing and dangling states. They do not prove
a ranked alphabet. The source deliberately rejects one symbol used at two
arities. This is a conversion error, rather than an empty language or a
solver result. The proof keeps that error.

## Exact normalization and validation

`FTAValidationClosed.normalized_closed` proves closure after actual map
normalization. `mkFTA_arity` reduces declared closed input to the exact
ordered arity scan. `mkFTA_ranked_iff` characterizes successful conversion
by its actual symbol/child-count declarations.
`arity_boundary` is a checked counterexample to unconditional success from
root membership and closure. One declared self-contained state uses the
same symbol at arities zero and one. Validation returns that arity error.

`SourceSizedFiniteKeysNormalized.normalized` retains raw constraints while
merging and sorting keys. `normalized_interpreted` identifies its result
with the actual normalized public FTA table. `normalized_graph` retains
the complete guarded row function, including alternative order.

`SourceFreshOrdinaryColdValidated` derives root membership and child closure
from any actual completed repaired cold traversal. It derives final resident
and replayed rows internally. `Trace.builder_equation` retains the literal
normalized arity scan. `builder_ok_iff` gives its exact success condition.
`builder_error` proves that every failed conversion is an arity failure.
No final heap metadata or supplied validation success is needed for these
control results.

## Independent language and staged public execution

`SourceFreshOrdinaryColdLiquid.Trace.liquid_language` identifies the validated
normalized raw graph with the independent guarded meaning of the original
physical root. It uses the general repaired cold language theorem. It needs
no prepared-cache or first-order restriction. `Trace.liquid_exact` derives
the complete common query specification for every successful actual encoded
fold over the validated output.

`SourceFreshOrdinaryLiquidEntry.Execution` follows the composition's stages.
Open roots return `openNode` and the identical constructor cache. Failed
validation returns `invalidFTA` before solver work. Successful validation
alone starts the encoded raw fold. The public result keeps conversion
errors, raised solver failures, GuardUnknown, and successful query records
in separate channels. Actual occurrence work remains in the fold trace.

`complete` derives a finite actual outcome from the initial semantic,
coverage, depth, and availability facts and finite external attempts.
`Execution.invalid_arity` proves the exact possible closed conversion error.
`Execution.exact_queries` proves all successful bounded query laws at the
original independent guarded root language. These include finite classes,
exact distinct node-count membership, counts, signed rejection, size-major
prefixes, accepted-term rank coverage, and both rank/unrank directions.

`complete_exact` combines finite actual execution and every successful query
law. `constructed_complete` derives all internal heap and root premises from
actual closed repaired construction. It supplies neither validation success
nor final metadata, native completion, or a language equation. External
attempt termination and response correctness remain explicit contracts.
Replies can vary by occurrence. All stopping channels retain their source form.

## Validation and preservation

The six new modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
audit passes 1,560 jobs and checks dependencies of 44,392 theorems. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-general-cold-liquid-entry-20261014-audit.log`.
Only the old unused `inputs` warning remains. No production Haskell code
changed. The active implementation retains the previous source validation.
No older proof module changed except audit imports. All repros and marked
drafts retain their bytes. Snapshot:
`/tmp/mcfta-general-cold-liquid-checkpoint-20261014-2331/` (1,940 Lean-tree files).

## Next source connection

Apply original-map `sizedReference` and optimized `sized` to this same actual
validated normalized cold table. Derive their raw active-equality invariant
from original checked annotations through actual construction and traversal.
Keep the FTA arity error, the Sized residual-guard error, and complete query
record equality. Reuse `SourceFreshOrdinaryColdConstraintHeap`, the normalized
raw graph theorem, and `SourceSizedFiniteKeysApiLaws`. The older cyclic-import
native entry remains a separate completed source path.

Preserve the optimized interned core and older constructor/equality targets.
Concrete containers, lazy scheduling, primitive resources, external solver
behavior, and verified Haskell extraction retain their boundaries. Push
completed checkpoints regularly. Do not deploy, send messages, or post to
the board. Check allowance and stop all work at 1% remaining or less.

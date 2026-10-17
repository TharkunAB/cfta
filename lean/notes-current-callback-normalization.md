# Current callback normalization and native histories

Updated: 2026-10-17 18:33 CEST. Proof commit is `c86f75c0`.
Source main is `c0cc8a05`, merged locally at `896b0a1c`.

The whole-library implementation proof remains open. This checkpoint adds
source invariants and causal native edge histories. It does not prove
general recursive outer completion or repeated-pass convergence.

## Root normalization

`SourceCurrentNativeRootErasure.union_request` retains the complete returned
pair of the actual union and root filter. Final bare-self erasure gives the
same pair as the stripped canonical union request at the original union's
returned heap. This includes singleton self. It also includes ordinary-row
merging after self removal. No absence premise removes either case.

`union_same` compares those erased results in two actual cache histories.
It requires equal ordered stripped source alternatives, available inputs,
normal source heaps, and growth of both actual filter returns into a common
heap. It does not require a future callback result law.

`SourceCurrentNativeRecordErasure.singleton` derives exact singleton replay
from Normal, UnionNormal, and availability. Normal alone permits a stored
all-ordinary union and is insufficient. `request` applies the root equation
to an actual returned record. `same` compares two such records at their
actual heaps. The stripped-alternative equality remains an explicit input.
The general source comparison must derive that input.

## Live fixed captures

`SourceCurrentNativeNormalizationInputs.support` retains fixed captured
names and varying lexical labels. `actual_free` gives exact raw free-name
membership for the actual completed source build. `fixed_origin` projects
a surviving fixed name to its captured source record.

`ordinary_fresh_fixed` derives freshness of the chosen ordinary argument
from the actual completed Depth callback. It requires freshness only for
live fixed support. A discarded capture can contain that ordinary name.
`reserved_fresh_fixed` derives freshness of the reserved interned argument
from physical availability and the actual missing-key reservation.

These facts do not yet compare the original normalized callbacks. A nested
unused smart binder can return an outer varying reference beside a fixed
ordinary alternative. Its warm branch needs a law about the earlier stored
body and ordinary probe. That law must follow from actual earlier source
construction. The simultaneous source comparison and stored-Mu law remain
open. No heap predicate that assumes the desired result closes this gap.

## Causal native edge histories

`SourceCurrentNativeEdgeHistory.completed` starts with empty native tables
and an actual completed checked trace. It derives a Writer for every
returned edge cell. The induction splits actual cold body traces before
their protected finish. Warm cells retain that earlier witness.

Writer retains the literal request, evaluating owner, body trace, states,
and one-step finish. Its public proposition does not expose a global root
prefix embedding or an event count. `query` derives compiler cleanliness
and physical fields internally for a literal requestNode trace.

`Writer.live` recovers the accepted source edge body for a live result.
The result retains the literal full conjunction guard and the ordered
zipped child calls with their actual states. The sentinel has an empty
child and cannot survive live-row normalization. Actual WorkInputs supply
child availability. No Original-child restriction is required.

`warm` and `query_warm` recover the Writer for the exact request of a later
actual ready demand. They retain the physical readiness and key-safety
premises. They do not construct general query completion or the outer
recursive schedule.

## Actual Local and Parent invariant transport

Eight SourceCurrentUnionNormal modules compose the constructor invariant
through the literal current workers. NativePrograms derives its compiler
certificate internally. Its request law needs no caller-supplied reached
instruction admission. ProjectionGate covers forest reads and the gate.
Merge covers comparison, selection, and the merge worker. Conjunction,
Targets, Edits, and Scan retain the invariant through their actual phases.

`SourceCurrentUnionNormalLocalParent.reduce` and `parent` reach the actual
Local.reduce and Parent.edge endpoints. Each theorem requires only initial
UnionNormal and the worker's actual arguments. Every stopping heap retains
UnionNormal. Failures, unresolved reads, and exhausted bounds are included.
No completion, closure, cap, semantic readiness, or future callback law is
assumed. These preservation laws do not prove successful completion.

## Haskell repair handoff

No Haskell behavior patch or new production defect is added. Source main
is `c0cc8a05`, merged locally at `896b0a1c`. Field-pool repair `b9219b9e`
is included. The retained Chain example returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque
pools. Root FINDINGS records the repair, reproducer, affected files,
validation, and upstream status before the historical failure report.

The unchanged source reuses its strict Nix all-component build, 798
examples plus golden, Fourmolu, and Cabal-gild validation. Component checks
do not establish the remaining current frontend and runtime adapters.

## Verification

The pinned Audit passes 3063 jobs and 67649 dependency checks. The worker
has 4 GiB MemoryMax, 4 GiB MemoryHigh, zero swap, and 375 MiB peak memory.
All 12 final strict source logs are empty. All canonical targets pass.
Only propext, Classical.choice, and Quot.sound are permitted.

The evidence directory is
`restart-evidence/20261017-callback-normalization/`. Its README and
checkpoint-validation.json identify the selected public and constructed
checks. Failed attempts retain their source snapshots and raw logs.
The Audit replays one older unused-variable warning. New strict source
checks and selected imported probes have no diagnostics.

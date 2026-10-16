# Independent review of actual caller result-cell steps

Reviewed the current root-owned SourceCurrentAllocatedPartialCallSteps.
No material defect found. Source SHA256: `b6b54b3ed08dffaed64202a2614ba94da37cb32d67a250baee2a0d05ab3db5d5`.

## Start and physical key

`node_start` and `edge_start` (lines 35–69) derive the actual stored owner,
its ready inherited value and resident input, exact candidate key equality,
and evaluating cell from the literal begin equation. The context is rebased
only after deriving unchanged checked/merge/fourth components. No stored
owner or desired owner law is supplied as a premise.

The hit endpoints (lines 73–101) use the actual ready observation and the
initial legitimate warm-cell invariant. The underlying theorem derives
whole-caller equality. The proof then uses the reflexive postcondition.
No body is run on a hit.

## Protected finish and semantic scope

Both finish endpoints (lines 104–168) consume the literal actual body and
its smaller postcondition, result residency, and owner law. These are
explicit induction hypotheses. The module does not derive a complete
mutual caller proof by itself. The postcondition's final Sound is not a
hidden owner result law: the structural frame derives that this exact
owner cell is still evaluating at the body return. Returned-result laws
are conditional on a returned phase.

The frame starts from the protocol derived from the running context.
Its node_running/edge_running property preserves the exact handle and
complete original request. The finish uses that protected evaluating cell
and installs the derived owner law. Physical key transport then derives
the requested candidate law from coherent resident input identity and ready
inherited keys. It does not equate arbitrary raw records or cached payloads.
Using the old running heap for this transport is valid: only the input
records must reside there. The result law interprets the embedded immutable
result record; result residency is separately established at the actual
returned heap. Effects and merge/fourth retention are transported through
the actual unchanged start components and literal finish state.

## Binder reconstruction

`node_binder` (lines 172–198) does not assume that reconstruction is an
identity operation. The supplied completed rebuild equation is compared
with a derived resident filtered-probe rebuild. Thus the actual result is
cleanup of the original Mu and the actual heap is unchanged. Only after
these equalities does the proof use a reflexive caller postcondition.
Cleanup language equality supplies the node law for every ambient and term.
ProbeHeap remains an explicit initial physical invariant; it is not inferred
from generic readiness. The full caller must preserve it along smaller
actual executions.

## Independent probes

Command:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-mutual-caller/call-public.lean
```

Terminal exit 0. Eight public axiom checks and full signatures pass for
node_refl, node_start, edge_start, node_hit, edge_hit, node_finish,
edge_finish, and node_binder. Three external integration kernels also pass:

1. node_finish_retains_owner composes the actual start, body frame, body
   postcondition, finish, and exact returned owner cell with candidate law.
2. edge_finish_retains_owner performs the same test for the separate edge
   table and actual original edge owner.
3. binder_call derives resident_rebuild from the started owner's physical
   input. It constructs the actual NodeBody.binder trace, derives its Post
   and law, then finishes the original owner and obtains the candidate law.
   No binder completion, body postcondition, or result law is supplied.

All 11 axiom probes report only propext, Classical.choice, and Quot.sound.
There are no errors, warnings, or sorryAx entries. The printed signatures
have expected concrete types and actual trace/state indices. The final
binder statement omits the unused Symbol/Value equality instances.

No source, Audit, docs, Haskell, or Git changes were made by this reviewer.
No Lake build was run. The root-owned imported olean was newer than the
reviewed source. General completion, central mutual invariant discharge,
GHC forcing/publication, concurrency, and machine identity adequacy remain
outside this component review.

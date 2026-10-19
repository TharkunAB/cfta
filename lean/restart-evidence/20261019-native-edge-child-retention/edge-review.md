# Same edge-writer native retention

Checked: 2026-10-19 13:04 CEST.

The source `SourceCurrentNativeEdgeWriterRetention.lean` has SHA256
`7b5af2c0be1a8da8d97c0feff7aa4dda6d93227fa94090b48f52c6638f96fa36`.
Its three public heads are `Written`, `Written.forget` and `edge_writers`.
The selected strict `edge-direct-3` completed with a zero-byte log.
The selected canonical `edge-canonical-1` completed 1171 jobs. It replays
only the existing ClosedCompletion:24:5 unused-input warning.
The selected `edge-public-1` checks all three explicit public signatures,
complete proof terms and axiom sets. It passes all eight printer checks,
with no omitted proof terms and only the standard three permitted axioms.
Its full log has 344597 bytes.

## Exact contract

`Written handle request result readerNative` retains one actual captured
edge-body entry, return, fuel and owner. It keeps the literal edgeBody
Trace and protected finish. It retains both physical heap-growth facts
and `Retained capturedBodyReturn.native readerNative` INSIDE the same
existential. It does not pair an old writer with an unrelated native
interval. The reader is a native state, not a separately supplied heap.

`Written.forget` removes only the native-retention field. It gives the
existing `NativeEdgeWriterGrowth.Written` at the reader's heap with the
same captured states and body trace.

`edge_writers history handle request result cell` derives the stronger
receipt for every actual returned edge cell at that same checked state.
The existing causal History is the only source premise. The theorem does
not require a new semantic output law, internal entry History, or a later
successful enclosing execution.

## Chronological proof

The private Recorded invariant assigns the stronger receipt to each ready
edge cell. Its later and change rules compose BOTH physical growth and
native returned-cell retention. The lookup and demand rules retain old
writers and exclude newly evaluating cells from the returned-cell cases.
A finish keeps existing writers and installs the exact new owner result.

The finite actual-trace induction uses the public node-retention module's
`trace_retained` for each real yielded step. It handles work, domain entry,
reference reads, optional binders and node/edge calls. Node lookup, demand
and finish can change the node table, so they explicitly retain that
family while carrying edge writers forward. Both native families remain
in the same Retained relation. A newly completed edge body stamps its
actual writer at its own return with reflexive native retention, before
its literal finish. Later actual instructions extend that same receipt.

The History induction starts with empty native tables. Physical advance
uses its actual heap growth and `advance_retained`. A completed trace
uses its existing Clean, Good and Fields premises. None is added to the
public producer. Cold calls publish the new witness; warm calls retain the
earlier one through all intervening actual phases.

## Consumer and limits

The new field permits an actual selected child suffix and makeEdge return
to compose into the captured reader. `NativeReferenceOrigins.forwarded`
can then use History at that reader. It need not assume History at an
active internal child entry. Root owns this separate child consumer.

This component does not assign native memo history to an arbitrary later
physical view. It does not infer whole-event observational origins,
selected Mu body/probe alignment, initial syntax ancestry, a renewal
measure or general termination. Those are separate proof obligations.

## Attempts and ownership

All five runs used Lean4.34.1 through the effective 4 GiB, zero-swap and
five-minute wrapper. Strict attempts 1 and 2 retain elaboration failures.
Attempt 1 needed explicit same-native-state transport and a separately
generalized Recorded induction. Attempt 2 exposed a shadowed handle in the
node-demand proof; deriving its retention before the inner edge-handle
binder fixed that reference. Neither failure is classified as a resource
failure. Strict 3, canonical 1 and full public 1 pass. The maximum recorded
peak is 223 MiB for the canonical build.

Counts: three owned public pairs, zero owned constructed pairs, zero
auxiliary pairs and five owned Lean runs. Arity owns the separate actual
cold/warm fixture. Root owns the child consumer and full Audit. Explicit
pins exclude all other owners' mutable files, root peaks, shared selections
and authority documents. Earlier frozen sources and evidence are unchanged.

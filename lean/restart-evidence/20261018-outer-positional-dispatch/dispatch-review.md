# Actual indexed outer dispatch

Frozen on 2026-10-18 at 04:57 CEST.

## Checked result

`walk_indexed` decomposes a completed literal outer walk at any present
input slot. It returns the exact earlier walk, child fuel, inherited
`descend`, node call, returned slot, later walk, and literal `Reached`
prefix. The identity is `fuel = childFuel + slot + 1`. The prefix uses
the original fuel and the exact earlier returned list. The suffix uses
the selected child fuel and the next inherited offset.

`edge_dispatch` first verifies an actual completed outer `edgeCall`.
Initial `Good`, `EdgeReady`, causal plain `GuardHeap`, and memo `Origins`
derive the returned Parent `EdgeLink`; no returned link is assumed.
An original raw-own footprint, original and returned child slots, and
an actual completed walk then identify the exact dispatched input.
A positive row of that input, with a present literal continuation,
produces `Below childIndex next source` and strict structural mass
`mass next < mass source`.

The literal prefix starts at the enclosing rows phase. It passes through
the completed Parent call, actual inherited combine, live children
branch, and indexed walk to the selected node call. Each complete caller
state and inherited descent stays in the statement. The Parent and walk
completion equations are past observations. The theorem does not produce
general outer completion from initial facts.

## Constructed execution

`OuterPositionalDispatchCheck.actual_dispatch` has no theorem inputs.
It builds a finite ordinary source from an empty interner. The root has
a plain row with one child. That child has a positive pair row with two
identical finite leaf children and own class `[[0],[1]]`. Covered actual
guard allocations derive the initial physical invariants, fields,
request readiness, and empty outer memo origins. The causal guard heap
and physical probe heap follow from source construction.

The fixture evaluates a cold Parent edge call and a complete outer walk.
It invokes `edge_dispatch` for slot 0 and continuation 1. The result
includes the exact reached node call and strict leaf-to-pair mass bound.
No future trace, completed graph, returned memo invariant, or output Link
is an input. The public theorem is an alias to the checked private proof;
the full public statement remains the same.

This example has a plain enclosing footprint. Its positive child has an
endpoint at 1, so it does not supply a repeated `(1,1)` footprint. It is
one actual handoff, not a producer of an infinite or full recursive
`Below` chain. Generated anchors need not occur in the initial source.
The remaining global obligations include consistent consecutive anchor
handoffs, all-active-node-key separation, and a bound on fresh calls.

## Validation and retained attempts

Production strict attempts 1 and 2 failed on proof elaboration and scope.
Attempt 3 checked the partial indexed-walk theorem. Attempt 4 checks the
final two-head module and has an actual zero-byte raw log. Canonical 1
passes 1849 jobs. It replays one unchanged old unused-variable warning
from `InternedFreshOrdinaryClosedCompletion`; the new direct check has
no warning. No production edits followed that canonical build.

Constructed attempt 1 failed on an unused simp argument, the edge
residency projection, and unbounded normalization reduction. Attempt 2
uses the existing bounded array-normalization receipt and fails only on
the incorrect linked-field projection. Attempt 3 has a zero-byte log.
All executed source snapshots, raw logs, metadata and limit readbacks
remain at their original numbered paths.

Selected public group `dispatch-public-1` contains two complete signature,
proof and axiom triples. Selected `dispatch-kernels-public-1` contains
one constructed triple. All eight explicit printer/linter options are
present. The selected logs have no diagnostic, omitted term, printer
failure or nonstandard axiom. Every selected execution ran with actual
4 GiB maximum, 4 GiB high and zero swap. The verifier checks these exact
bytes and limits. No old source, Audit, Haskell or authority document was
changed by this component.

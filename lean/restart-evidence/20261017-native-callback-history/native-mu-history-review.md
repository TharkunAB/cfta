# Native optional-binder publication history

The production source is `SourceCurrentNativeMuHistory.lean`.
Its SHA256 is `e8265d9773e43b5f76ee23859a94ad1bb34d431ae1277dee60924bce58bc0ffe`.
All earlier production sources and evidence directories remain unchanged.

The three public theorems return `Nonempty MuPublication.History` at the
actual stopping heap. They apply to successful and pending outcomes.

- `callback` uses the exact repaired `callback_eq` theorem. The raw build
  produces its source history. Root filtering adds no completed Mu payload.
  The initial marker must be Available. This condition includes issued
  provenance when the marker is an interned reference.
- `construct` uses the exact repaired `construct_eq` theorem. The source
  binder produces histories for both probes, reservation, body, publication,
  and an earlier winner when present.
- `maybeMu` uses `construct` for an actual used pair. An unused pair has the
  reflexive history at its unchanged heap.

The initial `SemanticHeap` and body availability derive the joint source
context for the encoded body and its actual leaves. No completed execution,
callback result oracle, desired stored law, cap, or annotation premise is
supplied. The bridge records execution history. It does not itself prove
normalized callback comparison or a whole native query result law.

## Selected evidence

Strict attempt 2 has an empty log and matches production byte for byte.
Canonical attempt 1 passes 535 jobs. Public attempt 1 checks all three
public theorems with explicit `#check @`, proof printing, and axiom printing.
All eight required printer/linter options are explicit in the probe.

Kernel attempt 2 contains one no-premise constructed integration. It builds
an open ordinary source body from an actual intersection reference. The body
contains a nested raw Mu and retains the used pair. Initial semantic facts,
availability, complete tables, and the source history are derived from the
actual source construction. The existing decoded completion producer derives
the native optional-binder return. The new theorem supplies its local history.
The integration composes the source and native histories from empty tables.
It then proves exact same-result warm replay at the first full returned heap.
It supplies no future graph, final heap law, or completed-run premise.
The public witness aliases its private checked proof for bounded printing.

The final public and integration probes have no diagnostics or omissions.
Their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
All selected jobs read back MemoryMax = 4294967296,
MemoryHigh = 4294967296, and MemorySwapMax = 0.

Failed strict attempt 1 and failed kernel attempt 1 remain at their original
immutable source and raw log paths. The failed kernel contains parser and
nested-selection errors; its printed `sorryAx` is excluded from validation.
Only the successful kernel attempt 2 is selected. No earlier evidence is
rewritten or reinterpreted.

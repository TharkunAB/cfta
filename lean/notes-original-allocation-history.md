# One causal history for original equality fields

`SourceEqualityOriginalAllocationHistory` derives the original allocation
inventory from one shared interner history. Source main is `5c53de80`.
The equality field constructor bodies are unchanged from `e16f3b50`.

## History and derived facts

`History.start` begins at a supplied interner. Each `construct` event uses
the interner returned by the preceding event and records the actual
successful equality constructor call. The original field list retains the
chronological event order. `interleave` permits actual atomic interner steps
between field constructors. It does not reset the interner.

`construct_steps` derives current validity and the literal atomic allocation
receipt from actual normalized constructor completion. `History.verified`
derives final interner validity, the complete initial-to-final atomic trace,
and every recorded field's retained Origin. Original allocations can be
hits, live insertions, or contradiction values. No lookup answer is assumed.

`History.inventory` derives all source literal origins when the recorded
history covers the original syntax's complete literal inventory. That
inventory includes children and stored binder bodies. `operations_valid`
derives valid empty completed-operation tables over the same final interner.
This initializes a declared cold operation scope. It does not reset warm
completed tables.

`resident_lookup` composes the inventory with actual original graph
construction. Every resident original edge has successful read-only field
lookup, exact original readback, ready storage, and physical constructor
readback. It retains the earlier constructor's actual allocation identity.

## Remaining source bridge

Actual GHC construction must still supply this causal history, initial
interner validity, and original literal coverage. The model does not claim
that arbitrary original normalized fields were already allocated. It does
not add allocation at class entry. Runtime demand, unsafePerformIO cache
publication, capacity, and the complete current caller remain separate.

The earlier SourceEqualityOriginalFieldOrigins and current class entry
proofs remain unchanged. Their generic per-field interface remains useful.
This new history derives that interface from one consistent execution.

## Validation

Focused build: 1,213 jobs. Four public history axiom probes pass with only
the permitted Lean foundations. Aggregate audit: 2,120 jobs and 52,960
dependency checks. The old unused `inputs` warning is the only warning.
Evidence uses `/tmp/mcfta-required-support-allocation-history-*` and
`/tmp/mcfta-required-support-root-probes-*`.

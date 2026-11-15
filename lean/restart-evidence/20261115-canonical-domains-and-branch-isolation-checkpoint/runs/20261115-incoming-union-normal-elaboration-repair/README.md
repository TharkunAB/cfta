# Incoming union-normal elaboration repair

Status: UNCOMPILED. Root must recheck all four probes.
The previous candidate failed. This packet claims no new proof credit.

The private log reports one blocked split and two unknown node-operation names,
with two cascading cases errors. No other diagnostic is hidden by this summary.
The first two target-query axiom reports were standard. Enabled-check and incoming
reports contained sorryAx from elaboration failure and receive no module credit.

This repair changes four proof locations:

1. Reduce the local guardResult binding with `dsimp only` after `unfold check`.
   The subsequent split then sees the literal enabled-check conditional.
2. Qualify both encodeNode references as SourcePruningEnumerationNodes.encodeNode.
3. Qualify the actual native lookup as SourcePruningEnumerationNodes.lookupNode.

All FOUR theorem headers are byte-identical to the frozen original. Step and
Receipt proofs are also unchanged. Imports, literal runtime calls, budgets,
initial premises and result projections remain unchanged. No resource, model,
future callback, completion, or extra invariant premise was added.

MINIMAL.patch gives the exact four-location change. PRESERVED-HEADERS.txt records
the raw headers. FAILURE-DIAGNOSTICS.txt includes every actual error diagnostic
from the failed private log. Primitive source headers and pins are copied from
the original packet. The old packet and private failure log remain unchanged.

Only this new packet was written. No compiler, live source, Git, board, Haskell
or /tmp operation was performed.

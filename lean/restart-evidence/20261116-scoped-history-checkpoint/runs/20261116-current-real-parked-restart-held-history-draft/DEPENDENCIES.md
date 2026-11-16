# Check order

Status: UNCOMPILED. Root owns all compilation and source promotion.

1. Check and build `SourcePruningEnumerationPrefixHeldHistoryAtOriginalBudget`.
   The frozen prefix packet has raw SHA256 `62bb2f5fbbdb734add8142f212c937423c9aef9d0a27d9d6029439882d35b35f`.
2. Add the ordinary import from `REQUIRED-TOP-IMPORT.txt` at the owner file top.
3. Append `APPEND.lean.txt` to the current owner file. The owner already contains
   the exact global depth predicate. Do not append its copied definition again.
4. Append `PROBES.lean.txt` after the code.

The proof uses the actual original-budget continuing-prefix and phase-admission
producers. They derive the retained Packet, restart decision, and mass bound.
The actual parked restart keeps the native caller. The original native lookup
therefore supplies the smaller-depth call without a future lookup premise.

`nodeReserved_fallback` extracts the existing recursive reservation. The proof
uses the existing seed growth facts. It does not prove another forecast engine.
The advanced seed and mass are resource forecasts. The executed work budget
remains exactly `workFuel`.

# SourcePruningEnumerationSelectedConstraintHeap

Every bounded actual selected-value preparation retains an arbitrary edge-constraint predicate in its returned heap. This includes failed exposure and pending unfolding. The successful specialization provides the same invariant without changing the worker.

Inputs still provide the internal semantic heap and available closed value. This is one heap invariant, not all failed-state or execution-cost obligations.

The actual Lake target and both public source/axiom reports passed in the project Nix shell with Lean4.34.1. Own reports use warnings as errors. An unrelated existing dependency warning can be replayed by Lake. No whole-library or CI claim is made.

Run from the repository root with the serial capped profile:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 python3 lean/restart-evidence/20261107-selected-constraint-heap/check.py
```

`check.py` builds the actual module, compiles its source and both axiom reports, checks the allowed axiom sets and source stability, and removes temporary reports. It prints actual diagnostics on failure. No archived build tree or source snapshot is required. A separate cold rebuild was not tested.

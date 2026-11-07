# EnumerationStateTraceAllocationBound

The actual Lake target and own-source theorem report passed in shell.nix with Lean 4.34.1. The report uses one worker and treats warnings as errors. checked.json records the source hash and all 32 public theorem axioms. Only propext and Quot.sound occur.

Every recorded core state of enumerateNode, enumerateEdge, enumerateOut, the modeled scheduler, and the complete default driver has counter at most its input counter plus the actual tree work. The bound includes failed branches, rejected branches, and intermediate states. The final worker laws need no valid-state, caller-resource, or successful-execution premise. They hold at every supplied fuel.

The work sums all processed alternatives. It does not count native graph, cache, container, union-find, callback, or machine operations. This theorem does not derive work or sufficient fuel from the original input. The traced scheduler is the core slot scan. Native cached-scheduler correspondence remains separate.

Run from the repository root, serially:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus CAPPED_UNIT=mcfta-enumeration-trace-allocation-bound HEAVY_PEAKS=/tmp/mcfta-proof-peaks.tsv /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 350 python3 lean/restart-evidence/20261107-enumeration-trace-allocation-bound/check.py
```

The checker uses the existing build tree and removes its temporary source report. No copied build tree or source archive is needed.

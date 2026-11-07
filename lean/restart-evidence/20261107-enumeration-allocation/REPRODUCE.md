# Enumeration allocation checks

Run this command from the repository root. It uses the project Nix shell and the
serial memory cap.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-allocation-reproduce \
  HEAVY_PEAKS=/tmp/mcfta-allocation-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 360 \
  python3 lean/restart-evidence/20261107-enumeration-allocation/check.py
```

The checker builds `MicroCFTA.EnumerationStateAllocation`. It then checks the source
and the four axiom reports with one Lean thread and warnings as errors. It accepts
only `propext`, `Classical.choice`, and `Quot.sound`. The source must stay unchanged
during the check. The temporary source report is removed when the check ends.

The lemmas apply to the actual Lean model operations. Initialization establishes
the counter, value count, finite UF support, bounded parents, and `Total`.
Ancestry inheritance changes only its ancestry field. Allocation returns the old
counter, increments the counter once, and adds one value slot. It preserves the
UF forest. It preserves the internal invariants at the new counter.

These lemmas do not bound how many allocations both complete workers perform.
They do not establish Haskell graph, cache, interner, or identity correspondence.
The complete worker bound must follow from the original inputs and requested size.
No Haskell implementation changed. No full-library or Haskell build is needed for
this proof increment. Historical source-audit failure and unknown coverage remain.
The kernel check does not recover that audit.

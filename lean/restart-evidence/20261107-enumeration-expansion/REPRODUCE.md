# Enumeration expansion checks

Run this command from the repository root. It uses the project Nix shell and the
serial memory cap.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-expansion-reproduce \
  HEAVY_PEAKS=/tmp/mcfta-expansion-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 360 \
  python3 lean/restart-evidence/20261107-enumeration-expansion/check.py
```

The checker builds `MicroCFTA.EnumerationStateExpansionBounds`. It then checks the
source and the axiom reports named in `theorems.json`. It uses one Lean thread and
warnings as errors. It accepts only `propext`, `Classical.choice`, and `Quot.sound`.
The source must stay unchanged during the check. The temporary source report is
removed when the check ends.

The quantitative scope is counter growth in the actual model node and edge
transitions. The cost uses the existing graph and fuel arguments. Equality
suspension allocates one UVar. Recursive node views allocate one UVar. Ordinary
children expand recursively. Terminal assimilation, node merging, and union do
not allocate. The proof composes these operations and preserves the difference
between value count and counter.

This is an internal bound for successful returns. The complete system still needs
one bound from the original inputs and requested size for both complete workers.
It must also cover all generated, returned, and subsequent states, including
intermediate states on failing branches. The variable-origin property for equality
trie descent remains a separate query-range obligation. No Haskell implementation
changed. No whole-library or Haskell build is part of this proof increment.

The kernel check does not recover the historical source audit. Its failure and
unknown coverage remain. No archived build tree or private Source copy is needed
to reproduce the mathematical checks.

# Determinization frontier checks

The first-fresh-position tuple generator has exactly the source tuple membership. Empty tuples occur only in the initial round. A later round cannot emit a tuple made only of old keys. This is a set view before the source tuple sort, not an equality of output sequences.

The source is `lean/MicroCFTA/SourceSizedDeterminizationFrontier.lean`.
The Haskell source is `cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.
No Haskell source changed for this proof increment.

Run from the repository root with the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-sized-determinization-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-determinization-frontier/check.py
```

The checker enters the project Nix shell. It builds the actual Lake module.
It checks the source again with own warnings as errors and prints every
public theorem's axioms. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. `checked.json` records the checked source hash and reports.
Temporary source/axiom reports are removed. No build tree or source archive
is needed. A clean rebuild, CI, and Haskell execution were not checked.

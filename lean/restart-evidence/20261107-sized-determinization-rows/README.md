# Determinization rows checks

The source Left original roots and Right subset states retain their exact languages and unique size classes. Right acceptance uses concrete row renaming. Left completeness uses the internal Closed property, which the Run module derives. Ordered map/set correspondence and final sort remain separate.

The source is `lean/MicroCFTA/SourceSizedDeterminizationRows.lean`.
The Haskell source is `cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.
No Haskell source changed for this proof increment.

Run from the repository root under the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-sized-determinization-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-determinization-rows/check.py
```

The checker enters the project Nix shell and builds the actual Lake module.
It checks the source with own warnings as errors and prints each public
law's axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted. `checked.json` records the checked source hash and reports.
Temporary reports are removed. No build tree or source archive is needed.
A clean rebuild, CI, and Haskell execution were not checked.

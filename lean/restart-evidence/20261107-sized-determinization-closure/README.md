# Determinization closure checks

Closed table coverage derives original-language completeness by finite-term induction. The invariant also supplies distinct count classes. This is an internal theorem. The Run module derives its invariant from actual bounded discovery.

The source is `lean/MicroCFTA/SourceSizedDeterminizationClosure.lean`.
The Haskell source is `cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.
No Haskell source changed for this proof increment.

Run from the repository root under the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-sized-determinization-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-determinization-closure/check.py
```

The checker enters the project Nix shell and builds the actual Lake module.
It checks the source with own warnings as errors and prints each public
law's axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted. `checked.json` records the checked source hash and reports.
Temporary reports are removed. No build tree or source archive is needed.
A clean rebuild, CI, and Haskell execution were not checked.

# Determinization discovery checks

The limit-first discovery controller has a computed recursion bound. Its 1024-key limit permits at most 1025 checking rounds, including the final checking round. The context and step function are generic. The theorem does not bound work inside step, instantiate that function with the complete row builder, or prove output-row completeness.

The source is `lean/MicroCFTA/SourceSizedDeterminizationDiscovery.lean`.
The Haskell source is `cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.
No Haskell source changed for this proof increment.

Run from the repository root with the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-sized-determinization-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-determinization-discovery/check.py
```

The checker enters the project Nix shell. It builds the actual Lake module.
It checks the source again with own warnings as errors and prints every
public theorem's axioms. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. `checked.json` records the checked source hash and reports.
Temporary source/axiom reports are removed. No build tree or source archive
is needed. A clean rebuild, CI, and Haskell execution were not checked.

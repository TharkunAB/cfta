# Finite Sized keys under structural validation

Current structural validation derives finite root and child membership. Existing finite restriction preserves guarded languages and exact first-occurrence size classes. Dense canonical sorting equals the derived finite worker row for row, including repeated alternatives. No uniform symbol arity is required.

The source is `lean/MicroCFTA/SourceSizedStructuralKeys.lean`.
The current Haskell sources are `cfta/src/Data/CFTA.hs` and
`cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.

Run from the repository root under the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-current-fta-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-structural-keys/check.py
```

The checker enters `shell.nix` and builds the actual Lake module.
It checks this source with own warnings as errors. It reports all public
laws and permits only `propext`, `Classical.choice`, and `Quot.sound`.
`checked.json` records the checked source hash and reports. Temporary
reports are removed. No source archive or copied build tree is needed.
No clean rebuild, CI, or Haskell execution is claimed. Total-work and
native identity, cache, interner, Eq/hash, and machine-Int bridges remain open.

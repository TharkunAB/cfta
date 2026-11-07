# Current structural FTA validation

Current mkFTA checks root membership and child closure. Symbols can use several arities. The optional mixedArity check is separate. The checked 0/1-arity example succeeds here and fails under the preserved legacy ranked-alphabet validator. This is a formalization coverage correction. No Haskell defect or code change is claimed.

The source is `lean/MicroCFTA/SourceFTAValidation.lean`.
The current Haskell sources are `cfta/src/Data/CFTA.hs` and
`cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.

Run from the repository root under the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-current-fta-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-current-fta-validation/check.py
```

The checker enters `shell.nix` and builds the actual Lake module.
It checks this source with own warnings as errors. It reports all public
laws and permits only `propext`, `Classical.choice`, and `Quot.sound`.
`checked.json` records the checked source hash and reports. Temporary
reports are removed. No source archive or copied build tree is needed.
No clean rebuild, CI, or Haskell execution is claimed. Total-work and
native identity, cache, interner, Eq/hash, and machine-Int bridges remain open.

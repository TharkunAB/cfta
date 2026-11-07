# Exact discovered key origins

Actual successful discovery returns exactly the target keys of its accumulated
choices. The proof carries target witnesses for known and current found keys
through the actual Evaluation. It does not require an origin invariant from
the caller. Each returned key is a sublist of the original state inventory.
Distinct original keys therefore give distinct members within every subset.
These are membership and relative-order laws. Native map iteration order
and actual Haskell Set/Map readback remain separate.

The source is `lean/MicroCFTA/SourceSizedDeterminizationOrigins.lean`.
Run from the repository root under the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-current-fta-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-determinization-origins/check.py
```

The checker enters `shell.nix`, builds the actual Lake target, and checks
this source with own warnings as errors and all four public axiom reports.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
`checked.json` records the source hash and reports. Temporary reports are
removed. No copied source/build tree is needed. No clean/CI/Haskell execution
or original-input total-work bound is claimed.

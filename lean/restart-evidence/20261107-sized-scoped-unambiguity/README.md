# Original root uniqueness from the scoped check

Source: `lean/MicroCFTA/SourceSizedScopedUnambiguity.lean`.
SHA256: `efdee2016f33500d46d08038f96e96b9260c2ab833bdb5b948e396c550aad24e`.

`checked.json` records 6 checked public laws. The actual Lake target
and this source passed in `shell.nix` with Lean 4.34.1. The own source/axiom
report used `-j1` and warnings as errors. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed. Read the source comment for the exact scope.
No whole-library CI, Haskell execution, native storage, or total-work bound
is established by this packet.

Run from the repository root. Keep heavy checks serial. The checker removes
its temporary source and axiom report. It copies no source or build tree.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-sized-scoped-unambiguity-recheck \
  HEAVY_PEAKS=/tmp/mcfta-scoped-plain-recheck-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-scoped-unambiguity/check.py
```

The checker prints a fresh JSON report. Compare its source hash and axiom
entries with `checked.json`. Earlier failed drafts remain marked in the
runtime handoff. Do not rerun unchanged checks without a new reason.

# Run multiplicity under canonical sorting

Source: `lean/MicroCFTA/SourceSizedRunPermutation.lean`.
SHA256: `3c0757bdb5f8e2081da698d53fee96a958657141922becc90338fd2fbdc5e1a0`.

`checked.json` records 5 checked public laws. The actual Lake target
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
  CAPPED_UNIT=mcfta-sized-run-permutation-recheck \
  HEAVY_PEAKS=/tmp/mcfta-scoped-plain-recheck-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-run-permutation/check.py
```

The checker prints a fresh JSON report. Compare its source hash and axiom
entries with `checked.json`. Earlier failed drafts remain marked in the
runtime handoff. Do not rerun unchanged checks without a new reason.

# Literal equal-child constraint classification

Source: `lean/MicroCFTA/SourceSizedEqualChildren.lean`.
SHA256: `038d64586fd1f2c972553c9101178895c88890394f737eee0dc558d26c89c8e5`.

`checked.json` records 12 checked public laws. The actual Lake target
and this source passed in `shell.nix` with Lean 4.34.1. The own source/axiom
report used `-j1` and warnings as errors. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed. Read the source comment for the exact scope.
No whole-library CI, Haskell execution, native storage, or total-work bound
is established by this packet. The explorer's round bound does not bound
tuple generation or total native work.

Run from the repository root. Keep checks serial. The checker removes its
temporary source and axiom report. It copies no source or build tree.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-sized-equal-children-recheck \
  HEAVY_PEAKS=/tmp/mcfta-conjunction-recheck-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-equal-children/check.py
```

The checker prints a fresh JSON report. Compare source hash and axioms with
`checked.json`. Earlier marked drafts remain in the runtime handoff. Do not
repeat unchanged checks without a new reason.

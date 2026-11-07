# Literal same-token transition tuples

Source: `lean/MicroCFTA/SourceSizedConjunctionTuples.lean`.
SHA256: `1970298b3c4d33a63ac0bb6420bd854e044fd124a3c200d6bd8cbbb24a807371`.

`checked.json` records 9 checked public laws. The actual Lake target
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
  CAPPED_UNIT=mcfta-sized-conjunction-tuples-recheck \
  HEAVY_PEAKS=/tmp/mcfta-conjunction-recheck-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-conjunction-tuples/check.py
```

The checker prints a fresh JSON report. Compare source hash and axioms with
`checked.json`. Earlier marked drafts remain in the runtime handoff. Do not
repeat unchanged checks without a new reason.

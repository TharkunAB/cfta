# Union-find support check

Run from the repository root.
The toolchain is selected by `lean/lean-toolchain`.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-uf-support-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 360s \
  python3 lean/restart-evidence/20261106-union-find-support/check.py
```

The script builds the new module in `shell.nix`.
It then checks the source and axioms with warnings as errors.
It checks all five support lemmas and allows only `propext`, `Classical.choice`,
and `Quot.sound` as axioms. It reads the current source.
It deletes its temporary report when the check ends.
The check does not need an archived build tree or a source copy.

The lemmas cover an empty forest, a functional write, the actual `put`,
and initialization from any input list.
`initialBound` computes the maximum listed identity plus one, or zero for an
empty list. Initialization requires no supplied support bound.
The `put` lemma derives its result from the previous support bound and the key.
These results do not establish the invariant for every worker transition.
They do not prove a common fuel bound or Haskell correspondence.
The kernel check does not recover the earlier source-process audit.

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
It checks all twenty-seven support and fuel lemmas and allows only `propext`, `Classical.choice`,
and `Quot.sound` as axioms. It reads the current source.
It deletes its temporary report when the check ends.
The check does not need an archived build tree or a source copy.

The lemmas cover initialization, writes, actual `findRoot`, `link`, and `union`.
`initialBound` computes the maximum listed identity plus one, or zero for an
empty list. Initialization requires no supplied support bound.
`ParentsBelow` also bounds every stored parent identity.
Initialization establishes this property without a premise.
Find and union preserve both internal bounds when they return successfully.
The query-growth corollaries compute an enlarged bound from the queried identities.
They require no separate premise that those identities are below the old bound.
The `put` lemma derives its result from the previous support bound and the key.
If a total forest has no stored key at or above `bound`, every query succeeds
with `bound + 1` fuel. This theorem needs no parent-target or query-range premise.
The proof counts distinct stored parent frames, then adds one terminal root step.
The initialization corollaries discharge both support and totality.
Union also has one computed successful fuel for both searches.
Its initialization corollary computes that fuel from the input and query identities.
These results do not establish worker allocation growth.
They do not establish the invariant for every worker transition.
They do not prove a common original-input worker bound or Haskell correspondence.
The kernel check does not recover the earlier source-process audit.

# Exact queries after derived closed rows

The five public laws include the original successful-discovery results.
The new closed_ordered_queries_exact composition accepts a derived closed
row graph and a concrete per-row permutation. OrderedOutput derives these
facts from actual ordered discovery, target grouping and canonical sorting.
The optimized worker retains the resulting graph order. The original four
public interfaces remain available.

Run the source-based check from the repository root:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-ordered-determinization-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-determinization-queries/check.py
```

The checker builds the actual Lake target in shell.nix and checks this source
with own warnings as errors and all five axiom reports. Only propext,
Classical.choice and Quot.sound are permitted. checked.json records the
current checked hash and reports. Older reports remain in Git history.
No copied tree, cold rebuild, CI or Haskell execution is claimed. Native
correspondence, current public routing and original-input total work remain open.

# SourceSizedGroupedPreparedRank

The actual Lake target and own-source theorem report passed in shell.nix with Lean 4.34.1. The own-source report uses one worker and treats warnings as errors. checked.json records the source hash and theorem axioms. The allowed axioms are propext, Classical.choice, and Quot.sound. This is a component proof check. It does not establish native Haskell execution or full CI.

Run from the repository root, serially:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus CAPPED_UNIT=mcfta-sized-grouped-prepared-rank HEAVY_PEAKS=/tmp/mcfta-proof-peaks.tsv /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 python3 lean/restart-evidence/20261107-sized-grouped-prepared-rank/check.py
```

The checker uses the existing build tree. It removes its temporary source report. No source archive or copied build tree is required.

# EnumerationStateWorkTrace

The actual Lake target and own-source theorem report passed in shell.nix with Lean 4.34.1. The own-source report uses one worker and treats warnings as errors. checked.json records the source hash and theorem axioms. The allowed axioms are propext, Classical.choice, and Quot.sound. This is a component proof check. It does not establish native Haskell execution or full CI.

Executable node, edge and selected-slot traces erase to the current ordered source results for every fuel. The tree retains intermediate and error states. Its work law sums every successful continuation and preserves failed and rejected work. Graph and union-find operations remain atomic. Input-derived sufficient fuel and native primitive costs remain open.

Run from the repository root, serially:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus CAPPED_UNIT=mcfta-enumeration-state-work-trace HEAVY_PEAKS=/tmp/mcfta-proof-peaks.tsv /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 python3 lean/restart-evidence/20261107-enumeration-state-work-trace/check.py
```

The checker uses the existing build tree. It removes its temporary source report. No source archive or copied build tree is required.

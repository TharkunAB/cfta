# Constraint variable-origin proof

Run from the repository root. Use the project Nix environment and the serial
memory cap. This command builds the actual module and checks both axiom reports.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-variable-origin-check \
  HEAVY_PEAKS=/tmp/mcfta-variable-origin-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 360 \
  python3 lean/restart-evidence/20261107-equality-variable-origin/check.py
```

The checker uses the installed pinned Lean toolchain through Lake. It checks the
source hash and permits only propext, Classical.choice, and Quot.sound. It deletes
its temporary report. No archived build tree or private Source copy is required.

The two theorems apply to the actual EnumerationState.descendScs alias. Each
output variable comes from an input constraint. An upper bound on the input
variables therefore holds for all output variables. The proofs introduce no
caller-supplied variable-origin premise.

This contract closes the descent dependency for reference-range reasoning. It
does not prove the complete workers' ranges, allocation bound, termination, exact
languages/counts/order/inverses, or correspondence with Haskell execution.

Historical SourceProcessFAIL and Root Original-Source upperUNKNOWN remain. No
Original Source, TYPE, or compiled interface was viewed for this proof. The
EqualityTrie per-Original receipt history remains UNKNOWN. The proof does not
recover that history. No Haskell code changed or fix was established.

# Actual enumeration reference bounds

Run from the repository root. This command builds the actual module and checks
every public theorem listed in theorems.json.

```sh
env XDG_RUNTIME_DIR=/run/user/1000 \
  DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  CAPPED_UNIT=mcfta-reference-bounds-check \
  HEAVY_PEAKS=/tmp/mcfta-reference-bounds-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 360 \
  python3 lean/restart-evidence/20261107-enumeration-reference-bounds/check.py
```

Use the project Nix shell and pinned Lean toolchain. Compare the reported source
hash with verification.json. The checker deletes its temporary report. It needs
no private Source copy, archived build tree, or historical rolebook.

The fixed internal cap covers the counter, union-find support and parent targets,
suspended variables in stored values, holes in stored fragments, holes in guard
obligations, and holes in the returned fragment. It preserves counter/value-count
agreement and UnionFind.Total.

The Node/Edge initial-state corollaries calculate the cap as one plus the actual
allocation budget. They need no supplied invariant or capacity. The general
computed-cap endpoints use before.counter plus that budget. Fixed-cap helper
contracts support subsequent expansion under one internally derived global cap.
Their capacity hypotheses are internal proof obligations, not the final worker
contract. Fresh suspension variables index their newly allocated value slot when
the incoming value-count/counter agreement holds.

The actual representative action succeeds with bound + 1 fuel from supported
Total forests. The actual union action succeeds with that fuel when parent
targets and both query IDs are below bound. These results concern the real
EnumerationState actions, not replacement actions.

These expansion preservation statements apply to successful returns. A global
cap is not proof that all existing references index the current value list. The
cap still uses the existing fuel argument. The full original-input/request-size
bound for BOTH enumerateOut/enumerateFully, all failing prefixes and total work,
exact languages/counts/order/inverses, native IDs, and actual Haskell/runtime
correspondence remain open. No new final caller resource or validity premise is
permitted. The optimized interned core remains the primary target.

No Haskell code changed or fix was established. No Original Source/replay/TYPE or
compiled interface was viewed for this checkpoint. Per-Original histories and
quotas are unchanged. Historical SourceProcessFAIL and Root Original-Source
upperUNKNOWN remain permanent. Kernel checks do not recover that old audit.

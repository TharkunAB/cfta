# EnumerationFlatReadBounds

Forest erasure computes the complete related comparison input. At representative and index fuel 2, the actual flat incoming/cache action preserves the complete older observation. This includes ordered raw rows, native failures, absent results, caller and query effects, the outer read core, and optional recovered caches. General gained/lost writes and slot reads also have fixed-bound comparisons.

The observation relation does not prove cache correctness from forest validity alone. Existing completion laws require the internal cache, caller, storage, realization, and request-range invariants. Native intersection and emptiness-check bounds remain explicit. This does not prove the whole worker, recursive exactness, native machine-Int bounds, or Haskell translation.

The actual Lake target and every public source/axiom report passed with Lean 4.34.1 in the project Nix shell. `checked.json` records that observation. `theorems.json` lists all 8 public laws. `check.py` builds the actual target, compiles the source and axiom reports with warnings as errors, checks the allowed axioms, and checks that the source did not change. It prints compiler diagnostics on failure.

From the repository root, use the required serial capped runner:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 python3 lean/restart-evidence/20261107-flat-enumeration-read-bounds/check.py
```

The temporary report is removed automatically. The script reuses the normal project build cache. No archived build tree or private source receipt is required. A separate cold rebuild was not tested.

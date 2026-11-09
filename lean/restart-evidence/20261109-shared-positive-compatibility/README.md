# Actual shared finite-depth resource compatibility

The checker builds the affected import frontier and the complete Audit.
It checks all affected source hashes before and after each build.
Use the serial 4 GiB cap, zero swap and one Lean thread.

Reproduce from any working directory under that cap:

```sh
python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261109-shared-positive-compatibility/check.py
```

All previous Audit bytes remain after the new imports. This check does
not prove complete source normalization, adequate source depth, source
enumeration size/order, both concrete inverse APIs or Haskell correspondence.

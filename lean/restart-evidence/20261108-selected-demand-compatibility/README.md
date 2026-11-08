# Selected demand conjunction compatibility

The live graph has 5,327 Lean modules. The changed
reverse-import closure has 1,781 modules. Its
27 outermost targets cover the full closure. This
includes independent source-worker, type, and signed-ranking roots outside
Audit. The source snapshot records every affected module.

The pinned Nix and Lake checks pass for every frontier target. Audit has
4,324 direct imports. It checks
87,216 imported theorems, including private helpers.
It permits only propext, Classical.choice, and Quot.sound. Source packets
explicitly check 267 public theorems in the 73 changed proof modules, including
71 new public theorems. Previous public theorem names remain.

Reproduce from the repository root under the existing serial 4 GiB
heavy-management cap:

```sh
python3 lean/restart-evidence/20261108-selected-demand-compatibility/check.py
```

The checker derives the root from this file. It checks all source hashes
before and after compilation. It requires effective memory.max/high of
4 GiB and memory.swap.max of zero. LEAN_NUM_THREADS=1 limits this build.
The global queue is unchanged. No retained /tmp directory is needed.

Both selected checked call adapters use actual demand sampling. All changed
public names remain. The packet proves component compatibility and this
selected model cutover. Shared lazy requirements, complete enumeration,
practical native capacity, and complete Haskell correspondence remain open.
No production Haskell file changes here. The earlier Audit command body
and historical root documentation remain exact. No build archive is stored.

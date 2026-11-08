# Demanded read receipts compatibility

The live graph has 5,305 Lean modules. The changed reverse-import closure
has 14 modules. Audit covers that closure and has 4,302 direct imports.
The source snapshot records every affected module. The existing Audit
commands and body remain unchanged. The 13 new imports precede them.

The project Nix and Lake Audit passes. It checks 87,041 imported theorems,
including private helpers. It permits only propext, Classical.choice, and
Quot.sound. The source packets check all 36 new public theorems explicitly.

Reproduce from the repository root under the existing serial 4 GiB
heavy-management cap:

```sh
python3 lean/restart-evidence/20261108-demanded-read-receipts-compatibility/check.py
```

The checker derives the root from this file. It checks source hashes before
and after compilation. It requires effective memory.max and memory.high of
4 GiB and memory.swap.max of zero. No retained /tmp directory is needed.

This packet proves component compatibility. It does not establish selected
demand-sampler adoption, full enumeration, practical fixed-width capacity,
or complete native Haskell correspondence. No Haskell file changes here.

# Same-return driver and shared requirement compatibility

The graph has 5,334 Lean modules. The complete changed reverse-import
closure has eight modules: seven new proof modules and Audit. Audit covers
the full closure. Its 4,331 direct imports expose 88,112 checked theorems.
Only propext, Classical.choice, and Quot.sound are permitted. The seven
own-source packets check all 52 new public laws with warnings as errors.
The larger imported theorem count also includes existing dependency roots.

Reproduce under the existing serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261109-shared-requirement-compatibility/check.py
```

The checker derives the repository root from its own location. It verifies
every affected source hash before and after compilation. It requires actual
memory.max/high of 4 GiB and memory.swap.max of zero. LEAN_NUM_THREADS=1
limits this build. No retained temporary directory or build archive is needed.

The same-return theorem composes the verified worker and the finite driver
at chosen recursive depth under explicit initial Room and Capacity.
The shared cells and row spines are checked primitives. The selected
worklist still uses eager requirements. Queue adoption, sufficient depth,
complete enumeration, exact source size and signed inverses, practical
native capacity, and full Haskell correspondence remain open.
No production Haskell file changes. The earlier Audit body remains exact.

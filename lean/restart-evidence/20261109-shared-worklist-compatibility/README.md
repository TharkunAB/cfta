# Finite shared-worklist compatibility

All 14 new source modules and 60 public laws pass strict own-source checks.
The graph has 5,348 modules. Audit covers the complete 15-module changed
reverse-import closure. Its 4,345 direct imports expose 88,308 checked
theorems, including private helpers. Only propext, Classical.choice, and
Quot.sound are permitted. The complete previous Audit file remains exact.

Reproduce under the existing serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261109-shared-worklist-compatibility/check.py
```

The checker derives the repository root from this file. It verifies each
affected source hash before and after compilation. It requires effective
memory.max/high of 4 GiB, memory.swap.max of zero, and LEAN_NUM_THREADS=1.
No retained temporary directory or build archive is required.

The new shared queue uses actual lazy row and requirement cells. Its total
iterator derives a finite execution graph without a caller work allowance.
Credits and vector dimension derive from the original tuple budget. Native
observation allowances remain explicit; the outcome may be an exact fault.
Queue drain does not yet establish table materialization or Boolean soundness.
The selected caller still uses the published R170 eager requirement path.
Full adoption, sufficient enumeration depth, exact source size/count/order/
signed inverses, practical native capacity, and full Haskell correspondence
remain open. No production Haskell file changes in this checkpoint.

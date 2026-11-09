# Cached shared-table compatibility

All eight new source modules and 32 public laws pass strict own-source checks.
The graph has 5,356 modules. Audit covers the complete
9-module affected closure. Its 4,353 direct imports expose
88,447 checked theorems, including private helpers. Only propext,
Classical.choice, and Quot.sound are permitted. The entire previous Audit
file remains exact after the eight new imports.

Reproduce under the existing serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261109-cached-materialization-compatibility/check.py
```

The checker derives the repository root from this file. It verifies every
affected source hash before and after compilation. It requires effective
memory.max/high of 4 GiB, memory.swap.max of zero, and LEAN_NUM_THREADS=1.
Portable reproduction passes from cwd=/tmp. No retained temporary directory
or build archive is required.

The actual original-query iterator returns an exact fault or a drained,
fully cached table that can be read without another native observation.
Credits, handle validity, and scheduling coverage derive internally. Native
observation allowances p/h remain explicit. No extra work fuel or future
completion premise is supplied. Query order is preserved.

Boolean soundness, selected caller adoption, sufficient enumeration depth,
exact source size/count/order and signed inverses, practical machine bounds,
and full Haskell correspondence remain open. Upstream main documentation
corrections are integrated and recorded in FINDINGS. Executable Haskell
definitions do not change in that merge.

# Reader row integration review

Frozen on 2026-10-18 at 00:04 CEST.

The fixture imports SourceCurrentNativeReaderRowLineage at source hash
2609deb0a873c845ff54dd5e47b867407c4bf80e7bcfb3a8d60f18ff9cebcba1.
It changes no production source.

The actual repaired source build produces an ordinary row with two ordered
children: an ordinary leaf and a productive raw Mu. The initial native tables
are empty. The fixture derives Good from the constructed heap and actual
allocated equality operations. An eight-step cold edge call requests both
children and completes edge cell 0. Actual constructor work then adds a row
and a distinct ordinary node. The next four-step node call acquires owner 2.
Its two-step ordinary body runs compileRows while owner 2 is evaluating.
That body takes a one-step warm edge hit and constructs the result node.
The actual finish changes owner 2 to the exact returned result.

The final reader History follows the initial history, cold edge call, actual
constructor work, and completed node call. Retained follows the actual finish.
The public test invokes rows_child with those derived facts at row index 0
and child index 1. It obtains the full symbol and conjoined guard, both ordered
source children, a historical completed Mu child call, Good at its two states,
and growth from those states to the final reader. It supplies no History at
the internal active owner and no future callback, completion, or row law.

The test verifies this concrete active-owner case. It does not prove general
outer progress or constrain historical child calls to the current body.
The full row guard is top. No nontrivial-guard fixture is claimed.

Final printer-free check: reader-row-kernels-6, exit 0 and zero-byte log.
Final complete proof probe: reader-row-kernels-public-1, one constructed pair.
The probe includes all eight explicit options and only the standard three
axioms. Attempts 1, 3, 4, and 5 failed and remain intact. Attempt 2 passed an
earlier, less explicit statement of the same fixture. No failed run is counted.
Every own run executes its immutable source snapshot with verified 4 GiB
MemoryMax and MemoryHigh and zero swap. The maximum observed peak is 658 MiB.
The copied fixture prefix is pinned in the component manifest.

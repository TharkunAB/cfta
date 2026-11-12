# A fixed numerical arity cap through the same native read

`SourceNativeReadArityHeap.Heap bound state` bounds child-list length for EVERY
actual physical edge record in state. `initial_heap` derives a cap from the
current issued inventory, using the existing source-profile arity sum.

`read_arity_heap` observes ONE existing `SourceEqualityProjectionRead.Read`.
Current semantic readiness, root availability, root closedness, and the current
heap cap imply the SAME cap at the SAME returned heap and at every returned row.
The proof follows actual construction, substitution, and exposure worklists.
It does not replace the numerical cap with a guard/path Fits predicate.

The existing edge_heap and node_heap constructor laws are now public.
Their proof bodies are unchanged. The separate native-bound-depth-heap-arity
packet preserves the cap through the SAME whole copy.
Full enumerator work and machine-integer correspondence remain separate.

The strict checker emits an explicit #check and an axiom report for every public
theorem. It checks the exact public declaration list and namespace. Own-source
warnings are errors. `checked.json` pins the source hash. Reproduce under the
existing serial 4 GiB heavy-management cap from the repository root:

```sh
python3 lean/restart-evidence/20261112-source-read-arity-heap/check.py
```

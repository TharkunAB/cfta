# Fixed arity through the same native bounded copy

boundDepth_observed_heap follows one actual successful execution. Current
semantic readiness, root availability, closedness, and the current physical
Heap cap imply the SAME cap at the SAME returned heap. The private observer
follows reads, ordered child scans, edge/node constructors, and local memo puts.
It retains physical readiness, growth, closed values, and live memo entries.

complete_exact_arity calls complete_exact ONCE. It retains its entire stable
cutoff/value/heap/memo receipt and exact language. It appends the initial
issued-inventory arity cap at the SAME returned heap. No cap or future output
supplier is added to the original current-input header.

The strict checker checks every public theorem by its exact namespace and
emits an explicit #check and axiom report. Own-source warnings are errors.
checked.json pins the source. Reproduce under the existing serial 4 GiB cap:

```sh
python3 lean/restart-evidence/20261112-native-bound-depth-heap-arity/check.py
```

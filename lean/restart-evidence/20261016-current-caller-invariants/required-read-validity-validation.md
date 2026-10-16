# Supplied required-path read validity

Source: lean/MicroCFTA/SourceCurrentAllocatedRequiredReadValidity.lean.
Frozen SHA256: 2b239de98a446a7c052b23c8bd6860e10f25d3cb91aa4081a02de94fb7a6e230.
The source has 157 lines. The frozen copy has identical bytes.

Pinned Lean 4.34.1 focused canonical build passed with 1251 jobs. Only the existing unused inputs dependency warning appears. No older proof source changed. The final direct source check passed without warnings.

All six public theorems have axiom reports and full signatures. Three integration kernels have three further axiom reports and signatures. Total: nine axiom reports and nine signature checks. Final logs required-read-validity-publicprobes-1.log and required-read-validity-kernels-2.log have no errors, warnings, or sorryAx. Only propext, Classical.choice, and Quot.sound appear.

The source directly inducts the supplied NodeReads, ChildrenReads, and RowsReads with their actual initial and final global table indices. Head follows its supplied ExposureReads. It invokes fixed-fuel exposure validity, then transports the same returned bundle across the actual makeNode suffix. Recursive node calls pass the head's actual returned tables to the body. Selected children, retained rows, and remaining rows use the physical effects of their exact underlying graph to derive intermediate semantic heaps, cost heaps, and residency. Constructors add no global memo calls. No separate deep read witness is identified by heap equality.

The head, node, children, rows, required, and requireAll endpoints derive final Valid, unfolding Extends, and exact unchanged query tables. Initial SemanticReady, CostHeap, appropriate Available/Values/Edges, and global Valid are explicit. Reads are supplied completed schedule receipts; this component does not construct general execution completion or assert a host forcing schedule. Open unrelated forest values are permitted.

The same_required_graph kernel derives physical Keeps, final SemanticReady, CostHeap, result Values, and final global validity from the same RequireAllReads compiled child graph. The two_required_calls kernel uses those derived intermediate facts and tables to validate a second supplied required call. The selected_position kernel constructs an actual selected child receipt from exact node and tail reads without a supplied intermediate memo-validity law. The first evidence-only kernel check failed to infer its found argument and emitted an automatic error placeholder. That raw log is retained but is not validation; the second check is clean. No proof source changed for that correction.

This is a component proof for the actual supplied read receipt. It does not establish general caller termination, GHC scheduling, external solver correctness, concurrent cache publication, or source identity representation.

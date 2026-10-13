# Source operand orientation for raw leaf intersection

The source `intersectOpen` orders distinct ordinary operands by their node
identities before it executes the Cartesian hash join. The prior physical
leaf model omitted this step. Its row-set result and progress statement
remained valid, but its constructor request order could differ. This was a
formalization correspondence gap. It was not a Haskell source defect.

`EqualityRawLeafProduct.intersect` now uses `orderedProduct`. It compares the
ordinary node identities and supplies the smaller operand first. The source
`intersectOpenEdge` does not perform another edge-order swap. It checks
arity, intersects children, and conjoins constraints in that selected order.
`intersect_nodes` gives the exact closed ordinary-node branch equation.

`intersect_empty_left` and `intersect_empty_right` prove that the expanded
model performs no row or node-cache requests when either operand is empty.
Thus the model agrees with the source early-empty branch as complete Work,
including cache effects. The whole-node identity shortcut still preserves
original raw guard syntax.

`orderedProduct_read` derives the same raw Cartesian interpretation from
commutative guard conjunction. `orderedProduct_certified` retains the actual
oriented request list. Strict progress, finite-target compilation, and all
runtime forest and fixed-point bounds now use that request sequence.

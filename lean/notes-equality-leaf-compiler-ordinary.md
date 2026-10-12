# Derived ordinary inputs for physical path workers

`EqualityLeafProjectionCompileOrdinary` proves that an occurrence compiler
with ordinary available leaves produces ordinary physical records. The
proof uses complete child payload readback on cache hits. Normalized parent
rows can therefore inherit the exact original child invariant.

`compile_ordinary`, `compileEdges_ordinary`, and `compileForest_ordinary`
cover nodes, retained original edges, and ordered child forests. The generic
leaf availability and ordinary-input conditions are both discharged for the
canonical admitted leaf builder by the actual nullary constructor.

`admitted_workers` derives successful finite edit and required-path execution
for every compiled admitted occurrence tree. It has no supplied ordinary
physical-input premise. The edit's leaf operation is a finite `Work` value;
this theorem establishes worker completion, not leaf semantic correctness.
The separate physical product theorem supplies canonical leaf readback.

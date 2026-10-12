# Recursive worker readback in a finite completed cache

`EqualityLeafProjectionWorkerReadback` follows the actual finite edit and
required-path worker computations. Each theorem uses their real intermediate
bind states. Cache growth and replay derive one common readback state.

`editChildren_readback` and `requireChildren_readback` recover the exact
ordered child result lists. The readback functions call the actual recursive
workers. Their option defaults are unreachable because ordinary-input
completion supplies a successful result for each child.

`editEdges_readback` derives the actual rebuilt edge list from these child
readbacks. `requireEdges_readback` first filters each original edge by its
original child arity. It then rebuilds only the retained rows. A rejected row
has no child computation and contributes no replacement edge.

`edit_node_readback` and `require_node_readback` derive the actual parent
constructor result. These are executable worker equations, not supplied
parent-correctness contracts. They preserve complete symbols, constraints,
child order, and physical cache readback. They apply to a nonempty edit list
without a root edit, or to a proper child requirement, respectively. The
existing direct-return equations cover unselected and root-only operations.

These theorems expose the canonical stored parent rows. The separate parent
normalization theorems compare those rows with retained duplicate and dead
original occurrences. The remaining stateful composition must prepare the
finite original occurrence requests in a common cache and join these two
results for each recursive parent and each equality pass.

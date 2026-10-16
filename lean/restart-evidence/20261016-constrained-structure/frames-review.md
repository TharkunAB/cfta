# Checked native frame scope

Reviewed: 2026-10-16T16:19:20+02:00.

The four helpers describe actual physical traces. `finishNode_split` and
`finishEdge_split` expose the reached physical finish check. They retain the
exact heap, operation state, native tables, and continuation state.

`node_body_cell` and `edge_body_cell` retain the exact evaluating request at
its handle through the compiled body. They use initial physical cache validity,
the actual body trace, the syntactic body condition, and the existing running
retention theorem. The literal finish then installs the returned result in
that same cell. These helpers do not require a result language, a structural
result certificate, final validity, or a future completion premise.

The two imported integration kernels combine an actual body trace with an
actual one-step finish trace. They derive the same returned owner, output
equality, exact full finish state, and unchanged heap and operations across
finish. They extract availability or edge residency from the reached physical
finish check. The node kernel also composes the literal bound body and finish
traces at their exact sum of fuels.

The helpers do not prove result availability without a physical finish check.
They do not prove finite-ordinary closure, either operand height bound, general
request completion, Haskell evaluation order, concurrency, or GHC correspondence.
Those obligations remain with their respective proofs. No source defect or
Haskell repair follows from this component.

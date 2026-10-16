# Independent review of the outer constructor budget recurrence

Reviewed on 2026-10-16 at 23:54 CEST. No material defect was found in the frozen `SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.lean`.

Lines 22-31 charge each original node for at most one final raw node request and for at most its original row bound times the row cost. The node cost includes the parent prefix before any returned descendant traversal. This matches `SourceCurrentAllocatedPartialGraph.lean:62-67,85-101`: Rows executes EdgeCall, then Descendants of the returned edge, then the original row suffix. The ordinary node is rebuilt after the rows return.

The child recurrence uses the produced parent profile `parentRows G R A H`, `max A 1`, and `GuardParent.outputLimit G` at the smaller ordinary height. It does not reuse the original child profile. Parent arity can become one when a rejected constructor returns the Empty sentinel. The maximum arity ceiling includes that branch. Parent height does not increase, so every returned child remains within the smaller height bound.

The edge formula adds one raw descendant edge request after child traversal. This charge is separate from the one checked parent constructor request already included in ParentE. Therefore a row can pay for both constructors. `descendantsNodes` and `descendantsEdges` at lines 43-49 use the supplied returned-edge profile directly and do not apply a second parent transform. They multiply by that edge's own arity. At row entry the caller supplies the widened parent arity `max A 1`.

The row suffix traverses original rows. Earlier returned rows are not appended as new work. Multiplying by the original R therefore matches the literal row loop. The node's original numeric envelope and raw guard envelope can increase below each parent while the ordinary height decreases. The functions do not assume a finite fixed key carrier or distinct producer pairs. Warm result hits can emit zero constructor Work and remain below these full-expansion budgets.

The parameter and height monotonicity proofs widen the same source order. `height_step` first increases the descendant recurrence height and then widens the parent-produced row envelope. ParentUniformBudgets.parameters_mono supplies the corresponding parent cost comparison. No monotonicity proof assumes an execution, result law, final capacity, or completion callback.

These are pure natural-number upper bounds. They do not produce an actual constructor Work trace, prove all finite prefix capacities, derive a reached-parent Plan, or count native/worker instructions. Equality interner operations and inherited payload size are outside these constructor request counts. General Mu and host forcing/HashMap correspondence remain separate.

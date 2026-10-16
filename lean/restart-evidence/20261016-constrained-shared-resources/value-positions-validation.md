# Value position accounting

Validated 2026-10-16 21:00 CEST.

The frozen source is `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryValuePositions.lean`.
SHA256: `f534a47e44037cfa3140ad06f97e566fd505918a22cee520670ee1521791544c`.

The count includes the root of each value. Empty has count one. Ordinary rows and child lists add every literal position, including repeated identities and rows. Reference, Mu, and union heads are opaque single positions. All profile bounds require the existing finite ordinary NodeShape or ChildrenShape, which excludes those heads.

`profile_node` proves `node value <= 1 + arity * OccurrenceBounds.edgeCount rows arity heightBound`. `profile_children` multiplies this expression by the exact forest length. `profile_forest` uses a supplied initial length upper bound. The proofs first relate value positions to the existing literal row occurrence count. They then use the existing input profile and height bounds. No availability, physical readiness, callback, execution, result, or future invariant premise is required.

The API also provides ordered append laws, root positivity, forest length, and selected-child/row bounds. These laws count source positions. This module does not yet prove that an actual edit executes at most one callback per counted position. That execution induction remains a separate caller resource obligation.

## Validation

- Direct attempt 3 completed with exit 0 and no diagnostics. Both unused-section-variable and unused-variable linters were enabled.
- The root-owned canonical build completed successfully: 397 jobs in `value-positions-canonical-build-1.log`.
- Imported public probes completed with exit 0: 18 full signatures and 18 axiom reports in `value-positions-public-1.log`.
- Imported integration probes completed with exit 0: 4 kernel signatures and 4 axiom reports in `value-positions-kernels-1.log`.
- Final direct, public, and kernel logs contain no errors, warnings, or `sorryAx`. Axiom reports use only `propext` and `Quot.sound`.

The four kernels establish these distinct cases:

1. Two Empty roots contribute two positions while their old ordinary node occurrence count is zero. The new zero-height forest bound includes both roots.
2. Two copies of the same two-Empty row contribute four child positions and one ordinary root. The new profile bound gives five despite repeated identities.
3. Two ordered forest prefixes combine their independently derived initial profile/height/length bounds. The result uses the sum of their declared lengths.
4. A literal selected child fits the enclosing profiled node's descendant position budget. The proof composes child membership, row membership, the new row-position relation, and the existing row occurrence bound.

Failed direct attempts 1 and 2 and their exact source copies are preserved. Attempt 1 used unsupported namespace-alias syntax. Attempt 2 used local function notation in a simp unfolding list. Attempt 3 fixes those elaboration errors and the root positivity proof. No production source changed after the final direct pass and canonical build.

No older proof, Haskell source, Audit, restart authority, Git state, or old evidence changed. This component supplies pure position bounds for later shared edit accounting. It does not close cumulative class/pass/outer constructor reservations or the whole-library objective.

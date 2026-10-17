# Independent fixed-source query sequence review

Result: no material defect found in `SourceCurrentConstrainedCapStaticQueries.lean` at SHA-256 `9839dd8299ce4a4d7c91660fa7ace7ac5b0e07aed1ff72c83d9a2dcf5bc26b06`.

## Initial resources and actual state order

`resources` (lines 36–41) reserves original node and edge key ranges and one finite source-domain inventory. The domain credit is `initial.next + 2^(source.nodes.next + source.nodes.next * source.nodes.next)`. It does not depend on the number of queries.

The private request certificate (45–57) uses operands available in that fixed original source. It transfers their availability to the current heap through the actual past growth and issued history. Its request starts in the empty domain and its scope remains that of the original source. It does not use an output profile or a future query.

`ranges` (62–69) applies the existing raw-prefix admission theorem to that certificate and the same initial resources. `retained` (72–83) applies the theorem to the supplied actual checked trace. Its resulting `Current` contains the entire domain allocation trace from the original initial cache. This is the important cumulative invariant. It does not replace the starting domain cache at each later query.

`complete` (86–110) constructs its own query with `TargetQuery.finite`. It supplies word checks derived from the fixed resources. It verifies that same actual receipt with `CurrentNative.step`, which derives the returned cap and current-heap contextual, joint-cell, and origin stores. The physical and semantic results refer to the same returned value and complete checked state. It requires initial `Ready`, inventory admission, `Current`, the current native invariant, and global validity. These are legitimate entry invariants. It requires no completed query, future `WordRanges`, later counter bound, or result law.

`Queries.cons` (120–123) indexes each receipt by the exact preceding return. `complete_many` (126–167) passes the produced inventory, readiness, current domain history, current native stores, and global validity into its shorter list induction. It composes machine extensions and moves earlier returned availability through the actual later growth. It keeps every actual receipt. No native table, equality state, global table, or constructor heap is reset. The final domain bound uses the single initial trace and inventory.

## Imported checks

The root canonical build passes 1365 jobs. It replays one old warning from `InternedFreshOrdinaryClosedCompletion.lean:24`; it emits no new-module warning. The root strict attempt 2 has an empty log and its snapshot equals the reviewed source.

The independent public probe checks all six declared public APIs with full explicit proof, universe, name, and deep-term settings. All six axiom/signature pairs pass. The integration probe has one substantive pair. Both final logs have exit code 0, no warnings, no errors, and no `sorryAx`. Only standard Lean axioms occur.

`two_initial_queries` derives `Resources` from raw initial counters and cache validity. It derives the initial `Current` with an empty actual history. It independently constructs the first full query receipt. It then independently constructs a second query at exactly the first returned checked state, using the first produced readiness, inventory admission, native invariant, and global validity. It supplies no later numeric bound or future successful graph. Its output retains both full receipts, the source-indexed two-step `Queries`, both actual past histories, the two caps, the composed machine and equality growth, and final global validity.

The integration also proves the cumulative missing-key potential inequality on the same final domain cache. It derives the final domain supply bound from that same history and one original inventory cardinality. It derives the final strict word limit from the one initial `room` inequality. The first failed kernel attempt used a wrong field name for equality growth. Its source and raw diagnostic log remain preserved. Attempt 2 passed; attempt 3 adds the explicit cumulative potential result and is the final clean probe.

## Scope

This is finite serial checked-query completion over operands available in one fixed original source. Initial warm readiness, inventory admission, and causal current native laws remain explicit. All requested pairs must have closed, available original operands and their supplied initial finite-depth caps. Results are returned and certified, but a generated result can be used as an operand under this theorem only if it also satisfies that original-source availability requirement.

The resource theorem derives checked request word ranges and cumulative domain allocation headroom. It does not bound total constructor allocation work or runtime. It does not establish general result-fed cumulative resources, arbitrary editor or class completion, selected outer termination, or Haskell/GHC execution correctness. No such broader claim is needed for the fixed-source sequence theorem.

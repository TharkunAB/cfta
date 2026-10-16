# Independent serial-history integration review

Reviewed at 2026-10-16 06:29 CEST. The parent reports both modules are frozen and the full audit passes 2294 jobs and 56040 dependency checks. This task read source only. It ran no build and changed no proof module.

No material defect, future-success callback, parent result-law premise, or fixed-model domain gap was found.

`WarmHistory.program` is the literal ordered `Code.walk`. In `walk_complete`, the head query runs before its tail. `WordRanges.before_bind` restricts the supplied whole-walk range contract to that head. After head completion, `after_body` uses its actual physical trace to derive ranges at the exact reached state. A second `before_bind` derives the tail contract. No successful tail or future per-query range callback is supplied.

The composed physical trace binds the head to the remaining walk, then binds the tail to the pure list constructor. Its trace fuel is the sum of head and tail trace fuels. Its value order is the original query order. The complete returned state includes native caches and the operation cache. Source heap growth, issued history, and operation-cache growth compose at the actual intermediate state.

Earlier returned values remain available through `tail.extension.available`. `done_retained` derives actual tail retention of prior published keys and returned cells. `completed_node` derives the head's returned cell from the head's actual completion. Their composition stores the head result at the final history state, alongside the tail's own literal memo receipts. No final-cell assumption supplies these conclusions. `Receipt.warm` uses those derived final cells to prove an exact two-step return with the complete final checked state unchanged. This warm theorem retains its explicit cacheable-key condition.

The empty history has a zero-length physical trace, empty ordered results, and the identical initial and final state. `Receipt.done` completes its pure result in one interpreter step. Duplicate queries require no distinctness premise. The induction preserves list order and multiplicity and executes each duplicate through the actual current memo state. Memo retention preserves the earlier literal result.

`ColdHistoryExact.operands` contains both operands of every query. Its constructor builds one fixed input interface from that list. Membership proofs derive both operands' Original, source residency, closedness, and validity in that exact interface. The source model, representative function, and rank family remain fixed throughout the walk. Empty native tables derive initial contextual and syntactic scope validity; later calls consume the preceding actual receipt. No desired language or whole-history completion premise is used to admit the caches.

Initial physical `Good`, `SemanticReady`, closed Original available operands, and whole-walk `WordRanges` remain explicit. The closedness contract concerns the finite operand inventory, not every value in the source heap. The result receipt provides each result's physical residency, cached free-list closedness, contextual law, exact intersection meaning, final cache invariants, and idle state. It does not itself add `CostHeap` or establish GHC/runtime publication, concurrency, concrete identity, or unrestricted machine capacity.

Reviewed frozen SHA256 values:

```
eb59b9b5f2f101a72446f42cc56c22e93af173c8e861d2dfa517ff2f2631860a  SourceCurrentAllocatedNativeWarmHistory.lean
3c5f76fd06580132c296be30bf86eed952e224558b6c26488a2d1afdb30a0ce0  SourceCurrentAllocatedNativeColdHistoryExact.lean
```

The owners' build and kernel-probe evidence is separate from this source review. No source mutation, build, Git action, or documentation change occurred in this review task. The only new file is this evidence note.

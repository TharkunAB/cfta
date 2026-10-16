# Independent review of completed checked targets

Read-only review of `SourceCurrentAllocatedTargetComplete.lean`, frozen SHA256 `1c000463a2386e431d217641d6b6c083c0874f2d3f31d11d5970db77b74f9cf7`. The raw graph is SHA256 `7685d0546656c13d3048580cc33abf1bd448da3b89be56ebf60bb9e6c7719395`.

## Verdict

No material defect found. The proof constructs actual operands, recursive tails, and checked native returns. It threads the same checked state, operation caches, merge table, and global bundle. The finite endpoints do not assume future successful native execution, a result language law, or final readiness.

## Actual-prefix range plan

`TargetGraph.FoldRanges` quantifies raw operand and raw tail returns. It asks only for native `WordRanges` at the literal tail return. It has no semantic result law, final cache validity, or completed checked intersection premise. `fold_complete` proves tail completion independently by induction, then uses the corresponding reached-prefix range obligation. The recursive first component supplies the tail's own plan after the actual head operand. Thus the range premise is not a future-success oracle. Reached machine bounds remain an explicit full-scope limitation.

## State and inventory order

The source at `Equality/Operations.hs:230` uses `foldr intersect n ns`. Its three operands are `head ∩ (last ∩ seed)`. The graph performs the head operand, recursive tail operands, then the checked request. It retains the same first-seed rotation and actual returned states.

`fold_complete` lines 187–202 passes `first.admitted` to the recursive tail. At the final checked request it uses the tail's actual inventory and state. The head remains available through the tail's Keeps. Both native operands are derived closed outputs. `TargetQuery.finite` computes the next finite inventory from that literal heap and appends the operands. No generated operand is assumed Original or admitted in an old inventory.

`Fold.verified` follows the given raw graph and uses `Step.verified` at the existing checked step. That theorem aligns the constructed completion with the supplied full returned state. There is no reset to an initial native machine or result memo.

## Open original siblings and language

Only `ForestClosed` for each selected path is required. Proper ordinary paths do not require unrelated siblings closed. Whole closedness remains explicit at a root projection or nonordinary recursive head as defined by PathDomain. Original captured values remain available through actual Keeps; their language is evaluated under the supplied ambient environment.

The final inclusion law is conditional on a nonempty path list and every path being proper. It preserves a common accepted selected subtree. The empty target returns EmptyNode and does not claim to contain arbitrary common terms. Projection and merge use language inclusion where exactness would be false. The final checked intersection uses the independently proved exact PCS law.

## Cache and memo retention

The head operand returns its actual merge table, and the tail starts with that same table. Checked intersections do not replace it. The final stored merge invariant grows through the checked query's actual Keeps; uniform `CacheCovers` is heap-independent and remains the explicit legitimate warm-table semantic premise. It is not inferred from physical Stored or At.

Global receipts compose actual operand reads with checked query receipts. The checked query has real primitive Runs and NoGlobal for the SAME bundle. `FoldReads` retains that query receipt, so global silence is not inserted as an unproved annotation.

`Receipt.fourth_correct` is exactly a transport theorem for a previously correct immutable fourth table through the derived Keeps. It neither inserts a new answer nor claims a runtime cache lookup/publication theorem. The fourth table is not an index of the raw target graph. Whole source forcing/publication and external cache-state transfer remain separate boundaries.

## Independent validation

Root focused log `target-complete-build-3.log` ends with success, 1278 jobs, only the existing unused-input warning. No independent Lake build was run.

Direct command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-checked-target/target-independent-probes.lean
```

Terminal status: 0. `target-independent-probes-1.log` preserves the complete output. It checks all five public theorem axiom sets and signatures, seven kernel compositions, and three named probe theorem axiom sets. Only `propext`, `Classical.choice`, and `Quot.sound` occur. There are no warnings or errors.

The kernels cover warm two-path completion, warm three-path completion, verification of any actual target, empty target exact state and merge-table identity, empty target global-bundle identity, fourth-table correctness retention, and two generated checked intersections. The latter derives both literal source heaps, both root-inventory equations, both full query receipts, and exact language `head ∩ (last ∩ seed)` from only initial invariants and reached-prefix word checks.

No reviewed source was edited. No compiled artifact was created in the evidence directory.

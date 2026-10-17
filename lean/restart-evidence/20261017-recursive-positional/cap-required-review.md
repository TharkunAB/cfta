# Cap preservation through completed Required reads

Reviewed: 2026-10-17 02:05 CEST.

The two additive modules preserve the cap of each supplied input through the same completed physical graph. They also preserve the causal `MuStored valid` predicate at the actual returned heap. No whole-heap guard predicate, desired result law, external body callback, or future completion premise occurs in their public inputs.

`SourceCurrentConstrainedCapExposure` exposes `collect`, `nodeEdges`, and `head`. Each endpoint takes `valid` and `capDepth` before the existing actual-read inputs. The ordered worklist preserves the cap of its pending values. Ordinary rows project their cap from the input value. Union alternatives keep the same depth. A Mu cap can only use the hereditary constructor. The proof extracts that annotation, uses the actual `Construction.unfold` result and causal store, then restores `Cap.plain capDepth`. The fallback after a nonordinary Mu result reads the original Mu at the actual returned heap. It does not replace that read with a different result or heap.

`SourceCurrentConstrainedCapRequired` exposes `node`, `children`, `rows`, and concrete current `requireAll`. Each endpoint takes `valid capDepth actual semantic costs available closed stored cap`. The rows endpoint takes initial resident rows in place of available values. The result is `MuStored valid after` and the corresponding cap predicate on the actual outputs. The mutual motives quantify over `capDepth`. A retained row visits children at `capDepth - 1`. At depth zero, these children are hereditary and the original row guard remains valid. At positive depth, the row guard is unrestricted. Literal `makeEdge` preserves its complete original guard and actual ordered output children. Literal `makeNode` derives the parent cap from actual resident output rows. Selected children and row suffixes receive the physical effects of their earlier calls. Rejected rows do not demand their removed children.

## Validation

- Exposure strict direct attempt 2: exit 0, zero-byte diagnostic log. Attempt 1 and its exact source are retained.
- Required strict direct attempt 1: exit 0, zero-byte diagnostic log.
- Canonical import build: exit 0, 1104 jobs. The copied raw log retains the historical dependency warning from `InternedFreshOrdinaryClosedCompletion.lean:24`.
- Imported public probe: seven axiom/full-signature pairs, exit 0, no diagnostics or `sorryAx`.
- Imported integration probe: three axiom/full-signature pairs, exit 0, no diagnostics or `sorryAx`. Failed integration attempt 1 and its exact source are retained.

The integration kernels construct a source/head/Required sequence from allowed closed syntax; construct two Required calls with the second call at the first actual return; and construct a literal kept-row graph with an arbitrary original guard above a hereditary frontier. The last kernel derives the exact returned symbol, full guard, and child list. It includes canonical constructor hits through the ordinary physical readback facts. No kernel assumes a future enclosing completed graph.

## Scope

These are preservation theorems for completed serial graphs. The integration kernels reuse the existing finite Required completion theorem for legitimate initial inputs. The production modules do not assert general recursive target, native intersection, selected-edit, or outer-worker completion. They add no machine capacity claim or Haskell lazy-runtime correspondence claim.

A positive cap bounds the finite ordinary constrained shell above hereditary recursive values. It does not imply that the current primary selection gate returns false. A false gate answer does not imply whole hereditary annotation either. In particular, a bare recursive reference must not be treated as evidence that its dereferenced body is plain. The cap predicate admits Mu only through its hereditary case, and the causal Mu store supports the actual unfolding.

The next projection proof can use `head` at the same cap depth and reduce the cap on each ordinary child selection. The next native intersection closure proof must separately justify binder reconstruction when a constrained shell meets a recursive value. This preservation component supplies no such result law.

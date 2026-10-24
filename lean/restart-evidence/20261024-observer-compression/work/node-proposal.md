# Unexpanded-node observation under compression frames

Source-only audit, 2026-10-24 02:09 CEST. HEAD `ae8970309774ea10a833b64de7945f48d50ff11e`. No compiler, repository edit, or board action.

The public Haskell `getUnexpandedNode` at `cfta/src/Data/CFTA/Enumeration.hs:1412–1417` calls `getUVarValue`, then returns the stored optional node from an unenumerated value. Enumerated and eliminated values return `Nothing`. It does not enumerate, inspect the graph, call an oracle, or change a value slot. The read still compresses the representative through `getUVarValue` at 423–428 and `getUVarRepresentative` at 415–420.

There is no corresponding Lean `getUnexpandedNode` definition in the current enumeration modules. The smallest additive definition, in a new observer module, is:

```lean
def getUnexpandedNode (fuel uv : Nat) : EnumerateM Symbol Guard (Option Nat) := do
  let value ← getValue fuel uv
  pure (match value with | .unenumerated node _ => node | _ => none)
```

`Nat` is the existing model's stored node ID. The projection must return that ID directly. It must not expand a node, test `Graph.node`, or convert an empty graph node into `none`. No equality instance or graph parameter is needed. Exact correspondence here uses the existing model of stored node IDs; it does not add a representation theorem for Haskell `Node symbol`.

Use `MicroCFTA.EnumerationCompressionFrame` and `MicroCFTA.EnumerationExecution`. A small `Frame.symm` record proof is needed for final-state composition; the current frame API has reflexivity and transitivity but no symmetry theorem.

The primitive paired read interface can be:

```lean
theorem getValue_congr
    (leftFuel rightFuel uv : Nat) (left right leftAfter rightAfter : State Symbol Guard)
    (leftValue rightValue : UVarValue Symbol) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (getValue leftFuel uv) left leftValue leftAfter)
    (rightRead : Success (getValue rightFuel uv) right rightValue rightAfter) :
    leftValue = rightValue ∧ Frame leftAfter rightAfter
```

Decompose each actual read with `getValue_success`. Its `found : UnionFind.Result` gives the actual root, stored size, returned forest, and raw slot. Transfer the right original path to the left forest with `frame.reaches ... .mp`. `UnionFind.reaches_unique` identifies both actual root IDs and sizes. `frame.values` identifies the two stored values at that common root. This uses the actual observations, not equality of their fuel bounds.

The left compression gives `Frame left leftAfter`. The right compression gives `Frame right rightAfter`, using totality transferred by `frame.total total`. Compose `leftReadFrame.symm`, `frame`, and `rightReadFrame`. All five nonforest fields and every root/size path remain in the final frame. Literal equality of the two final forests is neither needed nor asserted.

The exact observer theorem should retain both independent observations:

```lean
theorem getUnexpandedNode_congr
    (leftFuel rightFuel uv : Nat) (left right leftAfter rightAfter : State Symbol Guard)
    (leftNode rightNode : Option Nat) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (getUnexpandedNode leftFuel uv) left leftNode leftAfter)
    (rightRead : Success (getUnexpandedNode rightFuel uv) right rightNode rightAfter) :
    leftNode = rightNode ∧ Frame leftAfter rightAfter
```

Split the single bind on each side. The final pure actions identify their states and projected values. Apply the paired `getValue` result, then the literal value projection. No induction is needed.

A useful sufficient-bound theorem transfers an actual successful observer read:

```lean
theorem getUnexpandedNode_complete
    (leftFuel uv : Nat) (left right leftAfter : State Symbol Guard) (node : Option Nat)
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (getUnexpandedNode leftFuel uv) left node leftAfter) :
    ∃ rightFuel rightAfter,
      (∀ extra, Success (getUnexpandedNode (rightFuel + extra) uv) right node rightAfter) ∧
      Frame leftAfter rightAfter
```

The supplied left success derives an actual original path and stored slot through `getValue_success`. Transfer that path to the right input by `frame.reaches ... .mpr`, and transfer the stored slot by `frame.values`. `findRoot_terminates` supplies a right bound and actual returned forest. Path uniqueness identifies the found root with the stored root. Reassemble the right read with `getValue_success`; then add the pure projection. `getValue_moreFuel` extends this one successful right read with its identical final state. Finally use paired congruence. The bound is independent of `leftFuel` and may differ from it.

For a stand-alone existence theorem without a supplied read, use genuine source conditions: `Reaches left.representatives uv root size` and `left.values[root]? = some value`, together with the frame and global totality needed by the existing complete-frame API. Alternatively derive these from the caller's existing safety and in-domain facts. Do not add a premise that already states the observer's desired result.

`Total` plus `Frame` alone does not imply successful observation. The identical state with `UnionFind.empty` and no value slots is total and reflexively framed, but its canonical slot is absent. The Lean action returns `invalidSlot`; Haskell's `IntMap.!` is partial there. Fuel zero can also fail despite a readable root. Therefore this proposal proves paired successes and sufficient independent bounds, not equality of all bounded errors or exception behavior.

The native representative primitive already has exact conditional-compression/CPS correspondence through `SourceUnionFindCompression.findRoot_eq` and `EnumerationCPSUnionFind.representative_exact`. A later source observer CPS wrapper can compose that primitive with the existing slot read and pure projection. It must retain the same error/slot-validity boundary. No general oracle congruence follows: `ReadOnlyOracle` restricts successful state changes, not which output a callback computes.

Root can keep the primitive module small: `Frame.symm`, paired representative/getValue results if useful, the additive observer definition, its paired-success theorem, and its one-sided sufficient-bound theorem. Estimate 110–170 ordinary lines with existing APIs. There is no new recursive IH, scheduler execution, or driver proof in this slice.

Exact live API cuts:

- `EnumerationCompressionFrame.lean`: 20–52, 69–88 (`Frame`, transitivity/totality, actual representative/getValue frames); SHA `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375`.
- `EnumerationState.lean`: 103–124 (raw slot, representative, getValue); SHA `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.
- `EnumerationCorrectness.lean`: 37–46 (`Success`, bind decomposition), 1008–1035 (pure and actual getValue readback); SHA `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d`.
- `EnumerationExecution.lean`: 35–46 and 98–112 (successful retention, representative/getValue fuel extension), 413–419 (representative existence); SHA `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346`.
- `UnionFind.lean`: 45–64, 124–129, 160–199 (actual root/size uniqueness, read correctness, termination and bound extension); SHA `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14`.
- `EnumerationCPSUnionFind.lean`: 18–36 (actual source representative primitive); SHA `e4f2f6a29a5b1e686840b252d7618e8b0da698089e10f3a1be604028ac49e6b8`.
- Haskell `Enumeration.hs`: 415–428 and 1412–1417; SHA `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.

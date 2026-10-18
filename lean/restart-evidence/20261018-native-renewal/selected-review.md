# Selected positive continuation boundary

Frozen production: `SourceCurrentSelectedRenewalBoundary.lean`, SHA256 `10e5831681badf4d11083e567dda6795e9b9113060e263a0b7ac0d6580a32598`. Its one public theorem is a constructed literal-worker witness.

## Checked result

The source builds two ordinary input slots. The first has a positive root equality `[0]=[1]` and two plain middle children. The second has a plain root and two positive middle children. Every middle row has two identical leaf children. The source is built from the empty heap. Actual field allocations cover all source guards and derive initial weak physical Good. The original forest is available.

The chosen record is coherent, active and has exact paths `[[0],[1]]`. The literal primary worker returns false. The literal compiled `runClass` completes from the empty merge table. Output slot zero has a positive root row with a positive first child. This child equals the first child of an actual row in competing input slot one. It differs from the first child of every row in selected original slot zero.

The theorem derives `not PositionalOriginChain.Below 0 next selectedOriginal`. The proof does not use an output-shape assumption. Any such Below witness would give an indexed original row with exactly that child, contradicting the computed original children.

The initial inherited value has empty payload. The actual inherited-first accessor and combination on the returned root row complete. Actual descent at child zero returns empty inheritance again. The row's cross-child pair is therefore dropped while the positive continuation remains present.

This is a structural counterexample to unconditional original-slot positional anchor preservation after a selected native class edit. It is not a counterexample to the conditional Below theorem, whose exact retained-child premise remains correct. The child can still be smaller under another numeric measure. The theorem asserts no full outer ancestry, later Parent acceptance, accepted ground term, infinite execution, or Haskell defect. Its actual nonempty class result establishes the immediate native/class outcome only.

## Why existing APIs do not close this step

NativeNodeRowLineage already retains both indexed operand rows, full guards, and actual ordered child native calls. ClassSelectedChildLineage and ClassFoldRowOrigins already connect selected edit receipts to those queries. They do not make a product child identical to the selected original's child. Plain accepted recursive regions exclude positive rows, but this example is ordinary and the primary is false. That exclusion does not reject this class or force the selected-original identity.

A useful general renewal proof must retain the competing source lineage. It must relate later renewed positive fields to strict original occurrences across products, projections, Merge and Mu reconstruction, or prove a separate terminal rejection. This module supplies no global rank or desired source relation.

## Validation

`selected-direct-2` completes with a log of exactly zero bytes. `selected-canonical-1` completes and replays only the unchanged unused-input warning in InternedFreshOrdinaryClosedCompletion. `selected-public-1` prints the complete explicit statement, full public proof and standard axiom report under all eight required options. The public theorem is an exact-signature alias of a private checked existential witness. There is one public constructed boundary theorem and no additional fixture or auxiliary head.

Four owned Lean jobs use the pinned Lean 4.34.1 toolchain, a five-minute cap, memory.max=memory.high=4294967296 and memory.swap.max=0. Direct1 remains as an unselected failed attempt. Its structural computation goals passed; coverage disjunction simplification and unfolding of the named literal call required local proof fixes. No executable worker definition changes.

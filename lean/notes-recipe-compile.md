# Refinement recipe compiler correspondence

`MicroCFTA/RecipeCompile.lean` follows `microcfta-generator/src/Data/CFTA/Gen/Refinement/Internal/Compile.hs` at `d7f7c11`. It models the compiler's control decisions and selected metadata transformations. It does not model the complete output of `compileGen`. In particular, it does not assume an unspecified compiler is exact and then derive exactness from that assumption.

## Control decisions

`Generator` retains each recipe constructor and the independent stored source status. The model erases user values, callbacks, automata, and memo identifiers where the modeled control decision does not inspect them. A Boolean records whether the requested path set is empty. It does not record the paths themselves. Recipes are finite Lean trees. A cyclic source tag records the source representation; it does not encode a cyclic Haskell recipe graph.

The following definitions transcribe specific source decisions:

| Source functions | Lean definitions | Checked consequences |
| --- | --- | --- |
| `deferred`, `compile`, `compileGen` | `deferred`, `entryRoute`, `containsIntegers` | Only `SourceRequiresCompilation` requests compilation. Existing finite errors and cyclic sources pass through the entry route. Imported automata stop the integer search. |
| `compileGenOnce`, `compileOpen` | `closedRoute`, `openRoute` | `closed_integer_unreachable` and `open_impossible_unreachable` exclude the source's internal failure branches under their actual dispatch conditions. |
| `rootCount`, `spineRootCounts`, `alignedSpine`, `oneTermPart` | Definitions with corresponding names | Counts follow the source cases. Observation forwarding selects the unique one-root position. An empty choice has root count one. |
| Shape guards in `compileNode` and `compileOpenNode` | `shapeCheck` | `unobserved_shape` and `observed_shape` state exactly when alignment is required. |
| `emptyGroups`, `uniformWeights`, `chooseGroups` | Definitions with corresponding names | `chooseGroups_member` proves exact removal of known-empty alternatives and retention of original indices. Errors other than `EmptyGenerator` stay live. Recursive alternatives force unit weights before empty filtering. |
| `compileSpine`, `compileOpenSpine` product branches | `compileProduct` | Left-side errors and known-empty left sides prevent the right result from affecting the output. An empty product returns a successful outer result with a stored `EmptyGenerator`. |
| `constraintDecision` | `constraintDecision` | Acceptance occurs exactly for the actual `Yes` verdict. `Unknown` never becomes successful acceptance or rejection. The model preserves the diagnostic precedence. |
| `integerGroup` | `integerGroup` | A zero count removes the group. An unbounded integer leaf remains open. Other counting errors fail compilation. |
| Open-node settlement | `settle`, `retainedShare` | A tuple is removed exactly for count zero. A tuple with no open variables selects no artificial point. The accepted share uses one for each unknown child count, as the source does. |
| `settleGroups`, `closeOpen` error dispatch | `closeGroupedState` | A stored finite error remains nested inside success. Every cyclic source becomes a stored `UnboundedGenerator`. The successful finite worker is an explicit parameter. No law assumes this worker preserves values. |

The model of `chooseGroups` stops before `frequencies`. Weight validation, recursive equal-weight restrictions, map grouping, and final normalization are not consequences of `chooseGroups_member`. The closed-path `uniformWeights` model does not represent the distinct open-choice point-count and unbounded-choice checks.

## Integer holes and finite closure

`fillTerm` and `fillForest` implement the recursion in `fillHoles`. A user label receives the remaining point before its children consume coordinates. A placeholder consumes the next coordinate and becomes an integer leaf. Private labels retain their tag. The literal constructor and `exactLabel` remain explicit functions.

`fillTerm_remaining` and `fillForest_remaining` prove the exact remaining coordinate suffix. `fillTerm_holes` and `fillForest_holes` prove the exact number of unfilled placeholders. `fillTerm_exact` proves that a point whose length equals the hole count consumes every coordinate and fills every hole. These proofs establish traversal and consumption. They do not prove that `exactLabel` correctly constructs or simplifies a refinement. The hole count follows the source's replacement rule: a placeholder with children counts once because a supplied value discards those children. The source normally creates placeholder leaves.

`integer_closure_exact` uses `LatticeSelect.closePoints_exact`. It starts from successful parsing and successful construction of the actual polynomial levels. It concludes exact membership in finite value closure by all integer tuples satisfying the full formula semantics. It does not assume an exact point enumerator as a premise. This theorem uses the accepted integer lattice fragment and the value-level `ZeroSize.closePoints` model. It does not establish that the recipe compiler constructed the right formula, tuple reader, or term ranker.

`closeBucket_metadata` proves the size increment, Cartesian cardinality, unchanged outer mass, and multiplication of an explicit per-size mass by the point count. `closeBucket` also records that `pointsStatic` uses a non-atomic applicative result. `retainBucket` records the separate retained-share multiplication from settlement. `BucketMeta` describes one size class. It does not model all fields of `Static` or its sampler.

## Observation metadata and the confirmed distribution defect

`observedMember` follows the historical `groupBuilt` branch before the weight repair, after a member has been read. It retains that member's mass and size. For an atomic source, `sourceWeight` is `Nothing`, so the rebuilt bucket has no explicit per-size mass. For a non-atomic source, it carries the available within-size weight.

`pairBucket` follows `Gen/Internal/Grouped.hs`. Pairing multiplies outer masses and cardinalities, adds sizes, and makes the result non-atomic. It creates explicit per-size metadata only when one input already has it. `bucketSizeMass` follows `bucketMassIndex` in `Gen/Internal/Bucket.hs`: missing metadata defaults to count. `mergedSizeMasses` specializes the merge to components at one common size. It gives branch masses for that size. It is not the complete map merge or static sampler.

`atomic_pair_metadata_counterexample` checks the full metadata path for two observed atomic members with probabilities `9/10` and `1/10`. Pair each member with one ordinary leaf, then pay for the parent. Both outputs retain size three. Their unbounded first probability remains `9/10`. Both products have no explicit per-size mass and are non-atomic, so the common-size merge gives first probability `1/2`. This is the mechanism exercised by `atomicPair` in `repro/CurrentFindings.hs`. The current source retains the per-rank weight for atomic members. `MassRetention` proves the repaired path; `SizeTransport` proves the subsequent constructor-size shifts. This counterexample remains a check of the historical branch.

`observation_grouping_probability` composes the earlier `SizeMass.split_merge_probability` theorem. It proves event-probability preservation when grouping retains the complete positive member distribution. `observation_scale_probability` proves that the common nonzero rational scaling does not change normalized probabilities. Neither theorem states that all `groupBuilt` consumers retain the required metadata. `ObservationMass` and `GuardedSampling` prove the repaired finite partition/product/filter/merge path and its complete records. Heterogeneous recipe composition remains separate.

## Remaining compiler obligations

There is no theorem equating complete `compileGen` or `compileOpen` output with `validOutcomes` or with the user recipe's language. The following source work remains outside this module:

- Memo-table identity, `StableName`, `unsafeCoerce`, solver IO, and cyclic recipe evaluation.
- Construction and application of user-value functions through maps, products, choices, and computed labels.
- Requested-path propagation, `partRequirements`, observation reconstruction, key positioning, map ordering, and the complete regrouping algorithms.
- Formula construction in `integerDomain`, `renamedFormulas`, `partFormula`, `joinOpenKeys`, and open-node contracts. Variable offsets and tuple-reader splits need a proof that they use the same order as hole filling.
- Open-choice member weights, unbounded-choice rejection, and the complete finite workers in `settleGroups` and `closeOpen`.
- The complete `outcomeRanks` candidate search and the SpineView/LabelledView projections. `IntegerLiteral` proves canonical literal singleton construction and reading. `IntegerTermCodec` and `IntegerLabelCodec` derive WholeTerm fill/read and tuple-rank inverses. `OpenIntegerReaders` derives hole counts and coordinate order for bare applicative spines. See `notes-integer-term-codec.md`.
- Composition of import bounds, solver pruning, observation partitions, and final source reconstruction in `compileImport`.
- Complete distribution preservation through all combinations of observation grouping, products, settlement, and merging. The recorded atomic counterexample concerns the historical source. The repaired finite path has general distribution proofs, but a complete heterogeneous compiler theorem remains open.

Error payloads are reduced to categories or uninterpreted natural numbers. Counts and positions use unbounded naturals where Haskell sometimes uses `Int`. Rational arithmetic is exact. This is a source transcription with checked local laws, not extraction or verification of the compiled Haskell program.

Validation uses `lake build MicroCFTA.RecipeCompile` with the repository's pinned Lean toolchain. The strongest theorem dependencies use only Lean's standard logical axioms. No proof uses `sorry` or a project-specific axiom.
